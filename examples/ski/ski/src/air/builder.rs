use crate::air::pointer::Pointer;
use itertools::chain;
use wp1_core::air::{
    AirInteraction, BaseAirBuilder, ByteAirBuilder, ExtensionAirBuilder, WordAirBuilder,
};
use wp1_core::lookup::InteractionKind;

/// A custom AirBuilder trait that only includes
pub trait LurkAirBuilder:
    BaseAirBuilder
    + MemoSetBuilder
    + ConsBuilder
    + RelationBuilder
    + ByteAirBuilder
    + WordAirBuilder
    + ExtensionAirBuilder
{
}

pub trait MemoSetBuilder: BaseAirBuilder {
    /// Make a MemoSet query
    fn memoset_query(
        &mut self,
        tag: impl Into<Self::Expr>,
        values: impl IntoIterator<Item = Self::Expr>,
        is_real: impl Into<Self::Expr>,
    ) {
        self.send(AirInteraction::new(
            chain!([tag.into()], values.into_iter()).collect(),
            is_real.into(),
            InteractionKind::MemoSet,
        ));
    }

    /// Prove a MemoSet query (once!)
    fn memoset_prove(
        &mut self,
        tag: impl Into<Self::Expr>,
        values: impl IntoIterator<Item = Self::Expr>,
        multiplicity: impl Into<Self::Expr>,
    ) {
        self.receive(AirInteraction::new(
            chain!([tag.into()], values.into_iter()).collect(),
            multiplicity.into(),
            InteractionKind::MemoSet,
        ));
    }
}

//impl<AB: BaseAirBuilder> LurkAirBuilder for AB {}
impl<AB: BaseAirBuilder> MemoSetBuilder for AB {}

//pub trait LurkAirBuilder: BaseAirBuilder + ConsBuilder + RelationBuilder {}

pub trait ConsBuilder: BaseAirBuilder {
    /// Sends a byte operation to be processed.
    fn query_cons<E>(
        &mut self,
        a: Pointer<Self::Var>,
        b: Pointer<Self::Var>,
        c: Pointer<Self::Var>,
        is_cons: E,
    ) where
        E: Into<Self::Expr>,
    {
        self.send(AirInteraction::new(
            chain!(a.into_exprs(), b.into_exprs(), c.into_exprs()).collect(),
            is_cons.into(),
            InteractionKind::MemoSet,
        ));

        todo!("add cons domain");
    }

    /// Receives a byte operation to be processed.
    fn prove_cons<E>(
        &mut self,
        a: Pointer<Self::Var>,
        b: Pointer<Self::Var>,
        c: Pointer<Self::Var>,
        multiplicity: E,
    ) where
        E: Into<Self::Expr>,
    {
        self.receive(AirInteraction::new(
            chain!(a.into_exprs(), b.into_exprs(), c.into_exprs()).collect(),
            multiplicity.into(),
            InteractionKind::MemoSet,
        ));

        todo!("add cons domain");
    }
}

pub trait RelationBuilder: BaseAirBuilder {
    /// Sends a byte operation to be processed.
    fn query_relation<Etag, EReal>(
        &mut self,
        tag: Etag,
        a: Pointer<Self::Var>,
        b: Pointer<Self::Var>,
        is_real: EReal,
    ) where
        Etag: Into<Self::Expr>,
        EReal: Into<Self::Expr>,
    {
        self.send(AirInteraction::new(
            chain!(a.into_exprs(), b.into_exprs(), [tag.into()]).collect(),
            is_real.into(),
            InteractionKind::MemoSet,
        ));
        todo!("add relation domain");
    }

    /// Receives a byte operation to be processed.
    fn prove_relation<Etag, EMult>(
        &mut self,
        tag: Etag,
        a: Pointer<Self::Var>,
        b: Pointer<Self::Var>,
        multiplicity: EMult,
    ) where
        Etag: Into<Self::Expr>,
        EMult: Into<Self::Expr>,
    {
        self.receive(AirInteraction::new(
            chain!(a.into_exprs(), b.into_exprs(), [tag.into()]).collect(),
            multiplicity.into(),
            InteractionKind::MemoSet,
        ));
        todo!("add relation domain");
    }
}
