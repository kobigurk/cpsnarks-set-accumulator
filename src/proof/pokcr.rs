use crate::group::{multi_exp, Group};
use rug::Integer;

#[allow(non_snake_case)]
#[derive(PartialEq, Eq)]
pub struct PoKCR<G: Group> {
  w: G::Elem,
}

impl<G: Group> PoKCR<G> {
  pub fn prove(witnesses: &[G::Elem]) -> PoKCR<G> {
    PoKCR {
      w: witnesses.iter().fold(G::id(), |a, b| G::op(&a, b)),
    }
  }

  pub fn verify(alphas: &[G::Elem], x: &[Integer], proof: &PoKCR<G>) -> bool {
    let x_star = x.iter().product();
    let y = multi_exp::<G>(alphas, x);
    let lhs = G::exp_signed(&proof.w, &x_star);
    lhs == y
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::group::{GroupElemFrom, RSA2048};
  use crate::util::int;

  #[test]
  fn test_pokcr() {
    let witnesses = [RSA2048::elem(2u8), RSA2048::elem(3u8)];
    let x = [int(2), int(2)];
    let alphas = [RSA2048::elem(4u8), RSA2048::elem(9u8)];
    let proof = PoKCR::<RSA2048>::prove(&witnesses);
    assert!(proof.w == RSA2048::elem(6u8));
    assert!(PoKCR::verify(&alphas, &x, &proof));
  }
}
