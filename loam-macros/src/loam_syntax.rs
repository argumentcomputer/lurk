//! This file is largely taken from https://github.com/s-arash/ascent/blob/master/ascent_macro/src/ascent_syntax.rs

#![deny(warnings)]
use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

use proc_macro2::{Span, TokenStream};
use syn::parse::{Parse, ParseStream};
use syn::{
    braced, parenthesized, punctuated::Punctuated, spanned::Spanned, Attribute, Error, Expr,
    Generics, Ident, Pat, Result, Token, Type, Visibility,
};
use syn::{token, ExprMacro, ExprPath, Path};

use derive_syn_parse::Parse;
use itertools::Itertools;
use lazy_static::lazy_static;
use quote::ToTokens;

// resources:
// https://blog.rust-lang.org/2018/12/21/Procedural-Macros-in-Rust-2018.html
// https://github.com/dtolnay/syn/blob/master/examples/lazy-static/lazy-static/src/lib.rs
// https://crates.io/crates/quote
// example: https://gitlab.gnome.org/federico/gnome-class/-/blob/master/src/parser/mod.rs

mod kw {
    syn::custom_keyword!(relation);
    syn::custom_keyword!(lattice);
    syn::custom_punctuation!(LongLeftArrow, <--);
    syn::custom_keyword!(agg);
    syn::custom_keyword!(ident);
    syn::custom_keyword!(expr);
}

#[derive(Clone, Debug)]
struct Signatures {
    declaration: TypeSignature,
    implementation: Option<ImplSignature>,
}

impl Parse for Signatures {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let declaration = TypeSignature::parse(input)?;
        let implementation = if input.peek(Token![impl]) {
            Some(ImplSignature::parse(input)?)
        } else {
            None
        };
        Ok(Signatures {
            declaration,
            implementation,
        })
    }
}

impl ToTokens for Signatures {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let declaration = &self.declaration;
        let implementation = &self.implementation;

        tokens.extend(quote! {
            #declaration
            #implementation
        });
    }
}

#[derive(Clone, Parse, Debug)]
struct TypeSignature {
    // We don't actually use the Parse impl to parse attrs.
    #[call(Attribute::parse_outer)]
    attrs: Vec<Attribute>,
    visibility: Visibility,
    _struct_kw: Token![struct],
    ident: Ident,
    #[call(parse_generics_with_where_clause)]
    generics: Generics,
    _semi: Token![;],
}

impl ToTokens for TypeSignature {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let attrs = &self.attrs;
        let vis = &self.visibility;
        let ident = &self.ident;
        let generics = &self.generics;

        tokens.extend(quote! {
            #(#attrs)*
            #vis struct #ident #generics;
        });
    }
}

#[derive(Clone, Parse, Debug)]
struct ImplSignature {
    _impl_kw: Token![impl],
    impl_generics: Generics,
    ident: Ident,
    #[call(parse_generics_with_where_clause)]
    generics: Generics,
    _semi: Token![;],
}

impl ToTokens for ImplSignature {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let impl_generics = &self.impl_generics;
        let ident = &self.ident;
        let generics = &self.generics;

        tokens.extend(quote! {
            impl #impl_generics #ident #generics;
        });
    }
}

/// Parse impl on Generics does not parse WhereClauses, hence this function
fn parse_generics_with_where_clause(input: ParseStream<'_>) -> Result<Generics> {
    let mut res = Generics::parse(input)?;
    if input.peek(Token![where]) {
        res.where_clause = Some(input.parse()?);
    }
    Ok(res)
}

#[derive(Debug, Clone)]
struct RelationNode {
    attrs: Vec<Attribute>,
    name: Ident,
    field_types: Punctuated<Type, Token![,]>,
    _initialization: Option<Expr>,
    _semi_colon: Token![;],
    is_lattice: bool,
}

impl RelationNode {
    fn process_distillation_attributes(&self) -> bool {
        self.attrs.iter().any(|attr| {
            attr.path().is_ident("distill")
                && attr
                    .parse_args::<Ident>()
                    .map(|i| i == "preserve")
                    .unwrap_or(false)
        })
    }
}

impl Parse for RelationNode {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let is_lattice = input.peek(kw::lattice);
        if is_lattice {
            input.parse::<kw::lattice>()?;
        } else {
            input.parse::<kw::relation>()?;
        }
        let name: Ident = input.parse()?;
        let content;
        parenthesized!(content in input);
        let field_types = content.parse_terminated(Type::parse, Token![,])?;
        let _initialization = if input.peek(Token![=]) {
            input.parse::<Token![=]>()?;
            Some(input.parse::<Expr>()?)
        } else {
            None
        };

        let _semi_colon = input.parse::<Token![;]>()?;
        if is_lattice && field_types.empty_or_trailing() {
            return Err(input.error("empty lattice is not allowed"));
        }
        Ok(RelationNode {
            attrs: vec![],
            name,
            field_types,
            _semi_colon,
            is_lattice,
            _initialization,
        })
    }
}

impl ToTokens for RelationNode {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let name = &self.name;
        let field_types = &self.field_types;
        let attrs = &self.attrs;
        let kw = if self.is_lattice {
            quote!(lattice)
        } else {
            quote!(relation)
        };

        tokens.extend(quote! {
            #(#attrs)*
            #kw #name(#field_types);
        });
    }
}

#[derive(Debug, Parse, Clone)]
enum BodyItemNode {
    #[peek(Token![for], name = "generative clause")]
    Generator(GeneratorNode),
    #[peek(kw::agg, name = "aggregate clause")]
    Agg(AggClauseNode),
    #[peek_with(peek_macro_invocation, name = "macro invocation")]
    MacroInvocation(ExprMacro),
    #[peek(Ident, name = "body clause")]
    Clause(BodyClauseNode),
    #[peek(Token![!], name = "negation clause")]
    Negation(NegationClauseNode),
    #[peek(token::Paren, name = "disjunction node")]
    Disjunction(DisjunctionNode),
    #[peek_with(peek_if_or_let, name = "if condition or let binding")]
    Cond(CondClause),
}

fn peek_macro_invocation(parse_stream: ParseStream<'_>) -> bool {
    parse_stream.peek(Ident) && parse_stream.peek2(Token![!])
}

fn peek_if_or_let(parse_stream: ParseStream<'_>) -> bool {
    parse_stream.peek(Token![if]) || parse_stream.peek(Token![let])
}

impl ToTokens for BodyItemNode {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            BodyItemNode::Clause(clause) => {
                let rel = &clause.rel;
                let args = &clause.args;
                tokens.extend(quote! { #rel(#args) });
            }
            BodyItemNode::Generator(gen) => {
                let pattern = &gen.pattern;
                let expr = &gen.expr;
                tokens.extend(quote! { for #pattern in #expr });
            }
            BodyItemNode::Cond(cond) => cond.to_tokens(tokens),
            BodyItemNode::Agg(agg) => {
                let pat = &agg.pat;
                let aggregator = &agg.aggregator;
                let bound_args = &agg.bound_args;
                let rel = &agg.rel;
                let rel_args = &agg.rel_args;
                tokens.extend(quote! { agg #pat = #aggregator(#bound_args) in #rel(#rel_args) });
            }
            BodyItemNode::Negation(neg) => {
                let rel = &neg.rel;
                let args = &neg.args;
                tokens.extend(quote! { !#rel(#args) });
            }
            BodyItemNode::Disjunction(disj) => disj.to_tokens(tokens),
            BodyItemNode::MacroInvocation(mac) => mac.to_tokens(tokens),
        }
    }
}

#[derive(Debug, Clone)]
struct DisjunctionNode {
    _paren: token::Paren,
    disjuncts: Punctuated<Punctuated<BodyItemNode, Token![,]>, Token![||]>,
}

impl Parse for DisjunctionNode {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let content;
        let _paren = parenthesized!(content in input);
        let res: Punctuated<Punctuated<BodyItemNode, Token![,]>, Token![||]> =
            Punctuated::<Punctuated<BodyItemNode, Token![,]>, Token![||]>::parse_terminated_with(
                &content,
                Punctuated::<BodyItemNode, Token![,]>::parse_separated_nonempty,
            )?;
        Ok(DisjunctionNode {
            _paren,
            disjuncts: res,
        })
    }
}

impl ToTokens for DisjunctionNode {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let disjuncts = self.disjuncts.iter().map(|conj| {
            quote! { #conj }
        });
        tokens.extend(quote! { (#(#disjuncts)||*) });
    }
}

#[derive(Debug, Parse, Clone)]
struct GeneratorNode {
    _for_keyword: Token![for],
    #[call(Pat::parse_multi)]
    pattern: Pat,
    _in_keyword: Token![in],
    expr: Expr,
}

#[derive(Debug, Clone)]
struct BodyClauseNode {
    rel: Ident,
    args: Punctuated<BodyClauseArg, Token![,]>,
    _cond_clauses: Vec<CondClause>,
}

#[derive(Parse, Clone, PartialEq, Eq, Debug)]
enum BodyClauseArg {
    #[peek(Token![?], name = "Pattern arg")]
    Pat(ClauseArgPattern),
    #[peek_with({ |_| true }, name = "Expression arg")]
    Expr(Expr),
}

impl ToTokens for BodyClauseArg {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            BodyClauseArg::Pat(pat) => {
                pat.huh_token.to_tokens(tokens);
                pat.pattern.to_tokens(tokens);
            }
            BodyClauseArg::Expr(exp) => exp.to_tokens(tokens),
        }
    }
}

#[derive(Parse, Clone, PartialEq, Eq, Debug)]
struct ClauseArgPattern {
    huh_token: Token![?],
    #[call(Pat::parse_multi)]
    pattern: Pat,
}

#[derive(Parse, Clone, PartialEq, Eq, Hash, Debug)]
struct IfLetClause {
    if_keyword: Token![if],
    let_keyword: Token![let],
    #[call(Pat::parse_multi)]
    pattern: Pat,
    eq_symbol: Token![=],
    exp: Expr,
}

#[derive(Parse, Clone, PartialEq, Eq, Hash, Debug)]
struct IfClause {
    if_keyword: Token![if],
    cond: Expr,
}

#[derive(Parse, Clone, PartialEq, Eq, Hash, Debug)]
struct LetClause {
    let_keyword: Token![let],
    #[call(Pat::parse_multi)]
    pattern: Pat,
    eq_symbol: Token![=],
    exp: Expr,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum CondClause {
    IfLet(IfLetClause),
    If(IfClause),
    Let(LetClause),
}

impl Parse for CondClause {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.peek(Token![if]) {
            if input.peek2(Token![let]) {
                let cl: IfLetClause = input.parse()?;
                Ok(Self::IfLet(cl))
            } else {
                let cl: IfClause = input.parse()?;
                Ok(Self::If(cl))
            }
        } else if input.peek(Token![let]) {
            let cl: LetClause = input.parse()?;
            Ok(Self::Let(cl))
        } else {
            Err(input.error("expected either if clause or if let clause"))
        }
    }
}

impl ToTokens for CondClause {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            CondClause::If(if_clause) => {
                let cond = &if_clause.cond;
                tokens.extend(quote! { if #cond });
            }
            CondClause::IfLet(if_let_clause) => {
                let pattern = &if_let_clause.pattern;
                let expr = &if_let_clause.exp;
                tokens.extend(quote! { if let #pattern = #expr });
            }
            CondClause::Let(let_clause) => {
                let pattern = &let_clause.pattern;
                let expr = &let_clause.exp;
                tokens.extend(quote! { let #pattern = #expr });
            }
        }
    }
}

impl Parse for BodyClauseNode {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let rel: Ident = input.parse()?;
        let args_content;
        parenthesized!(args_content in input);
        let args = args_content.parse_terminated(BodyClauseArg::parse, Token![,])?;
        let mut _cond_clauses = vec![];
        while let Ok(cl) = input.parse() {
            _cond_clauses.push(cl);
        }
        Ok(BodyClauseNode {
            rel,
            args,
            _cond_clauses,
        })
    }
}

#[derive(Debug, Parse, Clone)]
struct NegationClauseNode {
    _neg_token: Token![!],
    rel: Ident,
    #[paren]
    _rel_arg_paren: token::Paren,
    #[inside(_rel_arg_paren)]
    #[call(Punctuated::parse_terminated)]
    args: Punctuated<Expr, Token![,]>,
}

#[derive(Debug, Clone, Parse)]
enum HeadItemNode {
    #[peek_with(peek_macro_invocation, name = "macro invocation")]
    MacroInvocation(ExprMacro),
    #[peek(Ident, name = "head clause")]
    HeadClause(HeadClauseNode),
}

impl HeadItemNode {
    fn clause(&self) -> &HeadClauseNode {
        match self {
            HeadItemNode::HeadClause(cl) => cl,
            HeadItemNode::MacroInvocation(_) => panic!("unexpected macro invocation"),
        }
    }
}

impl ToTokens for HeadItemNode {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            HeadItemNode::HeadClause(clause) => clause.to_tokens(tokens),
            HeadItemNode::MacroInvocation(mac) => mac.to_tokens(tokens),
        }
    }
}

#[derive(Debug, Clone)]
struct HeadClauseNode {
    rel: Ident,
    args: Punctuated<Expr, Token![,]>,
}

impl Parse for HeadClauseNode {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let rel: Ident = input.parse()?;
        let args_content;
        parenthesized!(args_content in input);
        let args = args_content.parse_terminated(Expr::parse, Token![,])?;
        Ok(HeadClauseNode { rel, args })
    }
}

impl ToTokens for HeadClauseNode {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let rel = &self.rel;
        let args = &self.args;
        tokens.extend(quote! { #rel(#args) });
    }
}

#[derive(Debug, Clone, Parse)]
struct AggClauseNode {
    _agg_kw: kw::agg,
    #[call(Pat::parse_multi)]
    pat: Pat,
    _eq_token: Token![=],
    aggregator: AggregatorNode,
    #[paren]
    _agg_arg_paren: token::Paren,
    #[inside(_agg_arg_paren)]
    #[call(Punctuated::parse_terminated)]
    bound_args: Punctuated<Ident, Token![,]>,
    _in_kw: Token![in],
    rel: Ident,
    #[paren]
    _rel_arg_paren: token::Paren,
    #[inside(_rel_arg_paren)]
    #[call(Punctuated::parse_terminated)]
    rel_args: Punctuated<Expr, Token![,]>,
}

#[derive(Debug, Clone)]
enum AggregatorNode {
    Path(Path),
    Expr(Expr),
}

impl Parse for AggregatorNode {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.peek(token::Paren) {
            let inside_parens;
            parenthesized!(inside_parens in input);
            Ok(AggregatorNode::Expr(inside_parens.parse()?))
        } else {
            Ok(AggregatorNode::Path(input.parse()?))
        }
    }
}

impl ToTokens for AggregatorNode {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            AggregatorNode::Path(path) => path.to_tokens(tokens),
            AggregatorNode::Expr(expr) => expr.to_tokens(tokens),
        }
    }
}

#[derive(Debug, Clone)]
struct RuleNode {
    attrs: Vec<Attribute>,
    head_clauses: Vec<HeadItemNode>, // Punctuated<HeadItemNode, Token![,]>,
    body_items: Vec<BodyItemNode>,   // Punctuated<BodyItemNode, Token![,]>,
}

impl RuleNode {
    fn process_distillation_attributes(&self) -> bool {
        self.attrs.iter().any(|attr| {
            attr.path().is_ident("with_bindings")
                || (attr.path().is_ident("distill")
                    && attr
                        .parse_args::<Ident>()
                        .map(|i| i == "preserve")
                        .unwrap_or(false))
        })
    }
}

impl Parse for RuleNode {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let head_clauses = if input.peek(token::Brace) {
            let content;
            braced!(content in input);
            Punctuated::<HeadItemNode, Token![,]>::parse_terminated(&content)?
        } else {
            Punctuated::<HeadItemNode, Token![,]>::parse_separated_nonempty(input)?
        };
        let head_clauses = head_clauses.into_iter().collect();

        if input.peek(Token![;]) {
            // println!("fact rule!!!");
            input.parse::<Token![;]>()?;
            Ok(RuleNode {
                attrs: vec![],
                head_clauses,
                body_items: vec![], /*Punctuated::default()*/
            })
        } else {
            input.parse::<Token![<]>()?;
            input.parse::<Token![-]>()?;
            input.parse::<Token![-]>()?;
            // NOTE this does not work with quote!
            // input.parse::<kw::LongLeftArrow>()?;

            let body_items =
                Punctuated::<BodyItemNode, Token![,]>::parse_separated_nonempty(input)?;
            input.parse::<Token![;]>()?;
            Ok(RuleNode {
                attrs: vec![],
                head_clauses,
                body_items: body_items.into_iter().collect(),
            })
        }
    }
}

impl ToTokens for RuleNode {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        // let attrs = &self.attrs;
        let head_clauses = &self.head_clauses;
        let body_items = &self.body_items;

        tokens.extend(quote! {
            #(#head_clauses),* <-- #(#body_items),*;
        });
    }
}

#[derive(Debug, Clone, Parse)]
struct MacroDefParam {
    _dollar: Token![$],
    name: Ident,
    _colon: Token![:],
    kind: MacroParamKind,
}

impl ToTokens for MacroDefParam {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let name = &self.name;
        let kind = &self.kind;

        tokens.extend(quote! {
            $#name:#kind
        });
    }
}

#[derive(Debug, Clone, Parse)]
#[allow(unused)]
enum MacroParamKind {
    #[peek(kw::ident, name = "ident")]
    Expr(Ident),
    #[peek(kw::expr, name = "expr")]
    Ident(Ident),
}

impl ToTokens for MacroParamKind {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            MacroParamKind::Expr(ident) | MacroParamKind::Ident(ident) => ident.to_tokens(tokens),
        }
    }
}

#[derive(Debug, Clone, Parse)]
struct MacroDefNode {
    _mac: Token![macro],
    name: Ident,
    #[paren]
    _arg_paren: token::Paren,
    #[inside(_arg_paren)]
    #[call(Punctuated::parse_terminated)]
    params: Punctuated<MacroDefParam, Token![,]>,
    #[brace]
    _body_brace: token::Brace,
    #[inside(_body_brace)]
    body: TokenStream,
}

impl ToTokens for MacroDefNode {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let name = &self.name;
        let params = &self.params;
        let body = &self.body;

        tokens.extend(quote! {
            macro #name(#params) {
                #body
            }
        });
    }
}

#[derive(Debug, Clone)]
pub(crate) struct LoamProgram {
    rules: Vec<RuleNode>,
    relations: Vec<RelationNode>,
    signatures: Option<Signatures>,
    attributes: Vec<Attribute>,
    macros: Vec<MacroDefNode>,
}

impl Parse for LoamProgram {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let attributes = Attribute::parse_inner(input)?;
        let mut struct_attrs = Attribute::parse_outer(input)?;
        let signatures = if input.peek(Token![pub]) || input.peek(Token![struct]) {
            let mut signatures = Signatures::parse(input)?;
            signatures.declaration.attrs = std::mem::take(&mut struct_attrs);
            Some(signatures)
        } else {
            None
        };
        let mut rules = vec![];
        let mut relations = vec![];
        let mut macros = vec![];
        while !input.is_empty() {
            let attrs = if !struct_attrs.is_empty() {
                std::mem::take(&mut struct_attrs)
            } else {
                Attribute::parse_outer(input)?
            };
            if input.peek(kw::relation) || input.peek(kw::lattice) {
                let mut relation_node = RelationNode::parse(input)?;
                relation_node.attrs = attrs;
                relations.push(relation_node);
            } else if input.peek(Token![macro]) {
                if !attrs.is_empty() {
                    return Err(Error::new(attrs[0].span(), "unexpected attribute(s)"));
                }
                macros.push(MacroDefNode::parse(input)?);
            } else {
                let mut rule_node = RuleNode::parse(input)?;
                rule_node.attrs = attrs;
                rules.push(rule_node);
            }
        }
        Ok(LoamProgram {
            rules,
            relations,
            signatures,
            attributes,
            macros,
        })
    }
}

impl ToTokens for LoamProgram {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let relations = &self.relations;
        let rules = &self.rules;
        let attributes = &self.attributes;
        let signatures = &self.signatures;
        let macros = &self.macros;

        tokens.extend(quote! {
            ascent! {
                #(#attributes)*
                #signatures
                #(#macros)*
                #(#relations)*
                #(#rules)*
            }
        });
    }
}

fn remove_distill_attributes(loam_program: &mut LoamProgram) {
    // Remove distill attributes from rules
    for rule in &mut loam_program.rules {
        rule.attrs.retain(|attr| !is_distill_attribute(attr));
    }

    // Remove distill attributes from relations
    for relation in &mut loam_program.relations {
        relation.attrs.retain(|attr| !is_distill_attribute(attr));
    }
}

fn is_distill_attribute(attr: &Attribute) -> bool {
    attr.path().is_ident("distill")
}

fn rule_desugar_with_binding(
    rule: &mut RuleNode,
    relations: &[RelationNode],
) -> Option<RelationNode> {
    let mut bindings = Vec::new();
    let mut binding_tys = Vec::new();

    // Parse the with_bindings attribute
    let binding_relation_name = rule.attrs.iter().find_map(|attr| {
        if attr.path().is_ident("with_bindings") {
            attr.parse_args::<Ident>().ok()
        } else {
            None
        }
    });

    for body_item in &rule.body_items {
        if let BodyItemNode::Clause(clause) = body_item {
            let relation = relations.iter().find(|r| r.name == clause.rel).unwrap();

            for (i, arg) in clause.args.iter().enumerate() {
                if let BodyClauseArg::Expr(Expr::Path(expr_path)) = arg {
                    if let Some(ident) = expr_path.path.get_ident() {
                        bindings.push(ident.clone());
                        binding_tys.push(relation.field_types[i].clone());
                    }
                }
            }
        }
    }

    if !bindings.is_empty() {
        let binding_relation_name = binding_relation_name.unwrap_or_else(|| {
            let join_clauses = rule
                .head_clauses
                .iter()
                .map(|hi| &hi.clause().rel)
                .join("_");
            let base_name = format!("{}_bindings", join_clauses);
            let unique_name = get_unique_name(&base_name);

            Ident::new(&unique_name, Span::call_site())
        });

        let binding_relation = RelationNode {
            attrs: Vec::new(),
            name: binding_relation_name.clone(),
            field_types: binding_tys.iter().cloned().collect::<Punctuated<_, _>>(),
            _initialization: None,
            _semi_colon: Token![;](Span::call_site()),
            is_lattice: false,
        };

        let binding_head_clause = HeadClauseNode {
            rel: binding_relation_name,
            args: bindings
                .iter()
                .map(|ident| {
                    Expr::Path(ExprPath {
                        attrs: Vec::new(),
                        qself: None,
                        path: Path::from(ident.clone()),
                    })
                })
                .collect(),
        };

        rule.head_clauses
            .push(HeadItemNode::HeadClause(binding_head_clause));
        Some(binding_relation)
    } else {
        None
    }
}

fn rules_desugar_with_binding(prog: &mut LoamProgram) {
    let mut new_relations = Vec::new();

    for rule in &mut prog.rules {
        if let Some(new_relation) = rule_desugar_with_binding(rule, &prog.relations) {
            new_relations.push(new_relation);
        }
    }

    prog.relations.extend(new_relations);
}

fn collect_relation_names(rule: &RuleNode, relation_names: &mut HashSet<Ident>) {
    for body_item in &rule.body_items {
        if let BodyItemNode::Clause(clause) = body_item {
            relation_names.insert(clause.rel.clone());
        }
    }
    for head_item in &rule.head_clauses {
        if let HeadItemNode::HeadClause(clause) = head_item {
            relation_names.insert(clause.rel.clone());
        }
    }
}

fn modify_signatures(original_signatures: &mut Option<Signatures>) {
    if let Some(signatures) = original_signatures.as_mut() {
        let ident = &mut signatures.declaration.ident;
        let new_name = format!("Distilled{}", ident);
        *ident = Ident::new(&new_name, ident.span());

        if let Some(impl_signature) = &mut signatures.implementation {
            let ident = &mut impl_signature.ident;
            let new_name = format!("Distilled{}", ident);
            *ident = Ident::new(&new_name, ident.span());
        }
    }
}

/// Compiles a Loam program into two Ascent programs. It expands the original program,
/// applying rule desugaring, and creates a distilled version containing only rules
/// with the `with_bindings` attribute and their associated relations.
pub(crate) fn compile_loam_to_ascent(loam_program: LoamProgram) -> TokenStream {
    // Stage 1: Expand the original Loam program
    let expanded_loam_program = expand_loam_program(loam_program.clone());

    // Stage 2: Distill the original Loam program
    let distilled_program = distill_loam_program(loam_program);

    // Generate the output
    let mut output = TokenStream::new();
    expanded_loam_program.to_tokens(&mut output);
    distilled_program.to_tokens(&mut output);
    output
}

fn expand_loam_program(mut loam_program: LoamProgram) -> LoamProgram {
    remove_distill_attributes(&mut loam_program);
    rules_desugar_with_binding(&mut loam_program);
    loam_program
}

fn distill_loam_program(mut loam_program: LoamProgram) -> LoamProgram {
    let mut relation_names = HashSet::new();

    // Process rules and drop those that shouldn't be preserved
    loam_program.rules.retain(|rule| {
        let should_preserve = rule.process_distillation_attributes();
        if should_preserve {
            collect_relation_names(rule, &mut relation_names);
        }
        should_preserve
    });

    // Process relations and drop those that shouldn't be preserved
    loam_program.relations.retain(|relation| {
        let should_preserve = relation.process_distillation_attributes();
        relation_names.contains(&relation.name) || should_preserve
    });

    // Modify the signatures for the distilled program
    modify_signatures(&mut loam_program.signatures);

    remove_distill_attributes(&mut loam_program);
    loam_program
}

lazy_static! {
    static ref NAME_COUNTERS: Mutex<HashMap<String, usize>> = Mutex::new(HashMap::new());
}

fn get_unique_name(base_name: &str) -> String {
    let mut counters = NAME_COUNTERS.lock().unwrap();
    let counter = counters.entry(base_name.to_string()).or_insert(0);
    *counter += 1;
    if *counter == 1 {
        base_name.to_string()
    } else {
        format!("{}_{}", base_name, counter)
    }
}
