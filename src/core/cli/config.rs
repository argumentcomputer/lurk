use camino::Utf8PathBuf;
use once_cell::sync::OnceCell;

#[derive(Debug)]
pub(crate) struct Config {
    pub(crate) lurk_dir: Utf8PathBuf,
}

impl Default for Config {
    fn default() -> Self {
        let home_dir = Utf8PathBuf::from_path_buf(
            home::home_dir().expect("Failed to retrieve home directory"),
        )
        .expect("Invalid home directory");
        let lurk_dir = home_dir.join(".lurk");
        Self { lurk_dir }
    }
}

static CONFIG: OnceCell<Config> = OnceCell::new();

pub(crate) fn set_config(config: Config) {
    CONFIG.set(config).expect("Config already set")
}

#[cfg(test)]
pub(crate) fn set_config_if_unset(config: Config) {
    let _ = CONFIG.set(config);
}

pub(crate) fn get_config() -> &'static Config {
    CONFIG.get().expect("Config hasn't been set")
}
