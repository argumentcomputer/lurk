use anyhow::{bail, Result};
use ratatui::{
    crossterm::event::{self, Event, KeyCode, KeyEventKind, KeyModifiers},
    layout::Size,
    style::{Style, Stylize},
    text::{Line, Span},
    widgets::{Paragraph, Wrap},
};
use rustc_hash::FxHashMap;

pub(crate) struct FormattedDebugEntry {
    pub(crate) dbg_depth: usize,
    pub(crate) formatted: String,
}

pub(crate) struct FormattedDebugData<'a> {
    pub(crate) entries: Vec<FormattedDebugEntry>,
    /// A map from depth to the indices of entries with the same depth
    pub(crate) dbg_depth_map: FxHashMap<usize, Vec<usize>>,
    pub(crate) breakpoints: &'a [usize],
}

impl FormattedDebugData<'_> {
    fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn entries(&self) -> &[FormattedDebugEntry] {
        &self.entries
    }

    fn entries_with_same_depth(&self, idx: usize) -> &[usize] {
        self.dbg_depth_map
            .get(&self.entries[idx].dbg_depth)
            .expect("Depth data missing")
    }

    fn next_eq_depth_idx(&self, curr_idx: usize) -> Option<&usize> {
        self.entries_with_same_depth(curr_idx)
            .iter()
            .find(|idx| idx > &&curr_idx)
    }

    fn prev_eq_depth_idx(&self, curr_idx: usize) -> Option<&usize> {
        self.entries_with_same_depth(curr_idx)
            .iter()
            .rev()
            .find(|idx| idx < &&curr_idx)
    }

    fn next_breakpoint_idx(&self, curr_idx: usize) -> Option<&usize> {
        self.breakpoints.iter().find(|idx| idx > &&curr_idx)
    }

    fn prev_breakpoint_idx(&self, curr_idx: usize) -> Option<&usize> {
        self.breakpoints.iter().rev().find(|idx| idx < &&curr_idx)
    }
}

/// Creates a vector of lines that can fit in the display.
/// Note: the last line may not fit entirely if it's too long.
fn produce_lines(
    entries: &[FormattedDebugEntry],
    display_idx_start: usize,
    focus_idx: usize,
    terminal_size: Size,
) -> Vec<Line<'_>> {
    let terminal_height = terminal_size.height.into();
    let mut lines = Vec::with_capacity(terminal_height);
    let mut total_height = 0;
    for (i, entry) in entries.iter().enumerate().skip(display_idx_start) {
        let style = if i == focus_idx {
            Style::new().black().on_gray()
        } else {
            Style::new()
        };
        lines.push(Line::from(Span::styled(&entry.formatted, style)));
        total_height += entry.formatted.len().div_ceil(terminal_size.width.into());
        if total_height >= terminal_height {
            break;
        }
    }
    lines
}

pub(crate) fn debug_mode(formatted_debug_data: &FormattedDebugData<'_>) -> Result<()> {
    if formatted_debug_data.is_empty() {
        bail!("No data to debug");
    }
    let entries = formatted_debug_data.entries();
    let last_entry_idx = entries.len() - 1;
    let mut display_idx_start = 0;
    let mut focus_idx = 0;
    let mut terminal = ratatui::init();
    loop {
        let lines = produce_lines(entries, display_idx_start, focus_idx, terminal.size()?);
        let display_idx_end = display_idx_start + lines.len() - 1;
        terminal.draw(|frame| {
            let paragraph = Paragraph::new(lines).wrap(Wrap { trim: false });
            frame.render_widget(paragraph, frame.area());
        })?;
        /// Moves the display to show the focused line
        macro_rules! adjust_display {
            () => {
                if focus_idx < display_idx_start || display_idx_end <= focus_idx {
                    display_idx_start = focus_idx;
                }
            };
        }
        if let Event::Key(key) = event::read()? {
            if key.kind != KeyEventKind::Press {
                continue;
            }
            let prev_focus_idx = focus_idx;
            match &key.code {
                KeyCode::Esc | KeyCode::Char('q') => break,
                KeyCode::Down => {
                    if key.modifiers == KeyModifiers::CONTROL {
                        display_idx_start = last_entry_idx.min(display_idx_start + 1);
                    } else {
                        focus_idx = last_entry_idx.min(focus_idx + 1);
                    }
                }
                KeyCode::PageDown => display_idx_start = last_entry_idx.min(display_idx_start + 1),
                KeyCode::Up => {
                    if key.modifiers == KeyModifiers::CONTROL {
                        display_idx_start = display_idx_start.saturating_sub(1);
                    } else {
                        focus_idx = focus_idx.saturating_sub(1);
                    }
                }
                KeyCode::PageUp => display_idx_start = display_idx_start.saturating_sub(1),
                KeyCode::Right => {
                    if key.modifiers == KeyModifiers::CONTROL {
                        if let Some(next_focus_idx) =
                            formatted_debug_data.next_breakpoint_idx(focus_idx)
                        {
                            focus_idx = *next_focus_idx;
                        }
                    } else if let Some(next_focus_idx) =
                        formatted_debug_data.next_eq_depth_idx(focus_idx)
                    {
                        focus_idx = *next_focus_idx;
                    }
                }
                KeyCode::Char(' ') => {
                    if let Some(next_focus_idx) =
                        formatted_debug_data.next_breakpoint_idx(focus_idx)
                    {
                        focus_idx = *next_focus_idx;
                    }
                }
                KeyCode::Left => {
                    if key.modifiers == KeyModifiers::CONTROL {
                        if let Some(next_focus_idx) =
                            formatted_debug_data.prev_breakpoint_idx(focus_idx)
                        {
                            focus_idx = *next_focus_idx;
                        }
                    } else if let Some(next_focus_idx) =
                        formatted_debug_data.prev_eq_depth_idx(focus_idx)
                    {
                        focus_idx = *next_focus_idx;
                    }
                }
                KeyCode::Backspace => {
                    if let Some(next_focus_idx) =
                        formatted_debug_data.prev_breakpoint_idx(focus_idx)
                    {
                        focus_idx = *next_focus_idx;
                    }
                }
                KeyCode::Home => focus_idx = 0,
                KeyCode::End => focus_idx = last_entry_idx,
                _ => (),
            }
            if focus_idx != prev_focus_idx {
                adjust_display!();
            }
        }
    }
    ratatui::restore();
    Ok(())
}
