use std::fmt;
use ff::{PrimeField, SqrtField, Field};
use super::{Engine, CurveAffine};
use crate::CurveProjective;
use super::{Bn256, G1, G1Affine, G2, G2Affine, Fq, Fq2, Fq12, FROBENIUS_COEFF_FQ6_C1, XI_TO_Q_MINUS_1_OVER_2, SIX_U_PLUS_2_NAF};
use crate::RawEncodable;
pub trait LineFunction: Copy + Clone + Sized + Send + Sync + fmt::Debug + fmt::Display + PartialEq + Eq + 'static + serde::Serialize + serde::de::DeserializeOwned {
    type Engine: Engine<Fr = Self::Scalar>;
    type Scalar: PrimeField + SqrtField;
    type Base: SqrtField;
    /// The projective representation of an element in G1.
    type G1: CurveProjective<Engine = Self, Base = Self::Fq, Scalar = Self::Fr, Affine = Self::G1Affine> + From<Self::G1Affine>;

    /// The affine representation of an element in G1.
    type G1Affine: CurveAffine<Engine = Self, Base = Self::Fq, Scalar = Self::Fr, Projective = Self::G1, Pair = Self::G2Affine, PairingResult = Self::Fqk> + From<Self::G1> + RawEncodable;

    /// The projective representation of an element in G2.
    type G2: CurveProjective<Engine = Self, Base = Self::Fqe, Scalar = Self::Fr, Affine = Self::G2Affine> + From<Self::G2Affine>;

    /// The affine representation of an element in G2.
    type G2Affine: CurveAffine<Engine = Self, Base = Self::Fqe, Scalar = Self::Fr, Projective = Self::G2, Pair = Self::G1Affine, PairingResult = Self::Fqk> + From<Self::G2>;
    /// The base field that hosts G1.
    type Fq: PrimeField + SqrtField;

    /// The extension field that hosts G2.
    type Fqe: SqrtField;

    type Fqk: Field;

    /// Compute the slope and intercept for point doubling.
    fn line_double(t: Self::G2Affine) -> (Self::Fqe, Self::Fqe);

    /// Compute the slope and intercept for point addition.
    fn line_add(t: Self::G2Affine, p: Self::G2Affine) -> (Self::Fqe, Self::Fqe);

    /// Compute the line function oracle.
    fn line_function(q: Self::G2Affine) -> Vec<(Self::Fqe, Self::Fqe)>;


}

impl LineFunction for Bn256 {
    type G1 = G1;
    type G1Affine = G1Affine;
    type G2 = G2;
    type G2Affine = G2Affine;
    type Fq = Fq;
    type Fqe = Fq2;
    type Fqk = Fq12;

    fn line_double(t: Self::G2Affine) -> (Self::Fqe, Self::Fqe){
        let x = t.x;
        let y = t.y;

        let mut alpha = t.x;
        let mut mu = t.y;
    
        // alpha = 3 * x^2 / 2 * y
        alpha.square();
        alpha.mul_assign(&Fq2::from(3u64));
        let mut tmp = t.y;
        tmp.double();
        tmp.inverse().unwrap();
        alpha.mul_assign(&tmp);

        let mut tmp = t.x;
        tmp.mul_assign(&alpha);
        mu.sub_assign(&tmp);

        (alpha, mu)
    }

    fn line_add(t: Self::G2Affine, p: Self::G2Affine) -> (Self::Fqe, Self::Fqe) {
    
        let x1 = t.x;
        let y1 = t.y;
        let x2 = p.x;
        let y2 = p.y;
    
        let mut alpha = t.y2;
        let mut mu = t.y1; 

        // alpha = (y2 - y1) / (x2 - x1)

        alpha.sub_assign(&y2);
        let mut tmp = x2; 
        tmp.sub_assign(&x1);
        tmp.inverse().unwrap();
        alpha.mul_assign(&tmp);

        let mut tmp = x1; 
        tmp.mul_assign(&alpha);
        mu.sub_assign(&tmp);
    
        (alpha, mu)
    }

    fn line_function(q: Self::G2) -> Vec<(Self::Fqe, Self::Fqe)> {
    
        let mut l = vec![];
        let mut t = q;
    
        for i in (1..SIX_U_PLUS_2_NAF.len()).rev()  {
            let (alpha, mu) = Self::line_double(t.into_affine());
            t = t.double();
            l.push((alpha, mu));
    
            if i != 0 {
                let q_t = if i == 1 { q } else { q.negate() };
                let (alpha, mu) = Self::line_add(t.into_affine(), q_t.into_affine());
                t = t.add(&q_t);
                l.push((alpha, mu));
            }
        }
    
        // Frobenius map calculations for BN256
        let mut pi_1_q_x = q.x; 
        let mut pi_1_q_y = q.y; 
        pi_1_q_x.conjugate();
        pi_1_q_x.mul_assign(&FROBENIUS_COEFF_FQ6_C1[1]);
        pi_1_q_y.conjugate();
        pi_1_q_y.mul_assign(&XI_TO_Q_MINUS_1_OVER_2[1]);
        let pi_1_q = Self::G2 {
            x: pi_1_q_x,
            y: pi_1_q_y,
            z: Fp2::one(),
        };

        let mut pi_2_q_x = q.x; 
        let mut pi_2_q_y = q.y; 
        pi_2_q_x.mul_assign(&FROBENIUS_COEFF_FQ6_C1[2]);
        let pi_2_q = Self::G2 {
            x: pi_2_q_x,
            y: q.y,
            z: Fp2::one(),
        };

    
        let (alpha, mu) = Self::line_add(t.into_affine(), pi_1_q.into_affine());
        t = t.add(&pi_1_q);
        l.push((alpha.into(), mu.into()));
    
        let (alpha, mu) = Self::line_add(t.into_affine(), pi_2_q.negate().into_affine());
        t = t.add(&pi_2_q.negate());
        l.push((alpha.into(), mu.into()));
    
        l
    }

}



