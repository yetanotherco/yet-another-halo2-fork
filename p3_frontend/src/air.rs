use p3_air::AirBuilder;

pub trait AirBuilderWithPublicValues: AirBuilder {
    fn public_values(&self) -> &[Self::Var];
}
