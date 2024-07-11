use p3_air::AirBuilder;
use p3_field::Field;
use std::borrow::{Borrow, BorrowMut};

pub trait AirGadget<F: Field>: AirGadgetBase<F> {}

pub trait AirGadgetBase<F: Field>: Sync {
    /// Native input for the gadget, usually `Self::InputAir<F>`
    type Input;
    /// Air input type, generic T allows `eval` to accept `T` defined through `AB`
    type InputAir<T>;

    type Output;
    type OutputAir<T>;

    type Witness<T>;

    type Record;
    type RecordAir;

    fn air_degree(&self) -> usize {
        3
    }

    fn witness_size(&self) -> usize {
        size_of::<Self::Witness<u8>>()
    }

    /// Given a pre-allocated witness, evaluate the gadget over the input while filling in witness
    /// values, and recording dependent events.
    fn populate_mut<W>(
        &self,
        input: &Self::Input,
        witness: &mut W,
        record: &mut Self::Record,
    ) -> Self::Output
    where
        W: BorrowMut<Self::Witness<F>>;

    fn eval<AB, I, IVar, O, OVar, W>(
        &self,
        input: &I,
        output: &O,
        witness: &W,
        record: &mut Self::RecordAir,
        is_real: impl Into<AB::Expr>,
    ) where
        AB: AirBuilder<F = F>,
        IVar: Into<AB::Expr> + Clone,
        OVar: Into<AB::Expr> + Clone,
        I: Borrow<Self::InputAir<IVar>>,
        O: Borrow<Self::OutputAir<OVar>>,
        W: Borrow<Self::Witness<AB::Var>>;
}

// TODO: The following are extension methods that could make sense to implement,
//       though they require additional bounds on Witness and Record. For now we can ignore them.
// pub trait AirGadgetExt<F: Field>: AirGadgetBase<F> {
//     /// Evaluate the gadget over the input, ignoring dependencies and witness generation.
//     fn execute(&self, input: &Self::Input) -> Self::Output;
//
//     /// Evaluate the gadget over the input, and record any dependent events.
//     fn generate_dependencies(&self, input: &Self::Input, record: &mut Self::Record)
//         -> Self::Output;
//
//     /// Same as `populate_mut` but returns a freshly allocated witness.
//     fn populate(
//         &self,
//         input: &Self::Input,
//         record: &mut Self::Record,
//     ) -> (Self::Output, Self::Witness<F>);
// }
//
// pub trait AirGadgetDefaultExt<F: Field>: AirGadgetBase<F>
// where
//     <Self as AirGadgetBase<F>>::Witness<F>: Default,
//     <Self as AirGadgetBase<F>>::Record: Default,
// {
// }
//
// impl<F: Field, G: AirGadgetDefaultExt<F>> AirGadgetExt<F> for G
// where
//     <G as AirGadgetBase<F>>::Witness<F>: Default,
//     <G as AirGadgetBase<F>>::Record: Default,
// {
//     fn execute(&self, input: &Self::Input) -> Self::Output
//     where
//         Self::Witness<F>: Default,
//         Self::Record: Default,
//     {
//         let mut record = Self::Record::default();
//         self.generate_dependencies(input, &mut record)
//     }
//
//     fn generate_dependencies(&self, input: &Self::Input, record: &mut Self::Record) -> Self::Output
//     where
//         Self::Witness<F>: Default,
//     {
//         let (output, _) = self.populate(input, record);
//         output
//     }
//
//     fn populate(
//         &self,
//         input: &Self::Input,
//         record: &mut Self::Record,
//     ) -> (Self::Output, Self::Witness<F>)
//     where
//         Self::Witness<F>: Default,
//     {
//         let mut witness: Self::Witness<F> = Default::default();
//         let output = self.populate_mut(input, &mut witness, record);
//         (output, witness)
//     }
// }

pub struct AirGadgetChip<G> {
    gadget: G,
}

// impl<F: Field, G: AirGadget<F>> BaseAir<F> for AirGadgetChip<G> {
//     fn width(&self) -> usize {
//         todo!()
//     }
// }
//
// impl<'a, F: Field, G: AirGadget<F>> WithEvents<'a> for AirGadgetChip<G> {
//     type Events = ();
// }
//
// impl<F: Field, G: AirGadget<F>> MachineAir<F> for AirGadgetChip<G> {
//     type Record = ();
//     type Program = ();
//
//     fn name(&self) -> String {
//         todo!()
//     }
//
//     fn generate_trace<EL: EventLens<Self>>(
//         &self,
//         input: &EL,
//         output: &mut Self::Record,
//     ) -> RowMajorMatrix<F> {
//         todo!()
//     }
//
//     fn included(&self, shard: &Self::Record) -> bool {
//         todo!()
//     }
// }
