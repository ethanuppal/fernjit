pub fn sign_extend_to<
    In: num_traits::Unsigned + num_traits::PrimInt + num_traits::AsPrimitive<Out>,
    Out: 'static + num_traits::Unsigned + Copy,
>(
    value: In,
    bits: u32,
) -> Out {
    let sign_bit = In::one() << (bits as usize - 1);
    if value & sign_bit != In::zero() {
        let extension = !((In::one() << bits as usize) - In::one());
        value | extension
    } else {
        value
    }
    .as_()
}
