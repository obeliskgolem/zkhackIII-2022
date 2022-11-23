use ark_ff::Zero;
use ark_ff::{to_bytes, FftField};
use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment, QuerySet};
use ark_std::rand::RngCore;

use ark_poly::{univariate::DensePolynomial, EvaluationDomain, Polynomial, UVPolynomial};
use ark_poly_commit::LabeledCommitment;

use crate::{
    data_structures::{Proof, Statement},
    error::Error,
    rng::FiatShamirRng,
    PROTOCOL_NAME,
};

pub fn prove<
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    FS: FiatShamirRng,
    R: RngCore,
>(
    ck: &PC::CommitterKey,
    statement: &Statement<F, PC>,
    f: &LabeledPolynomial<F, DensePolynomial<F>>,
    f_rand: &PC::Randomness,
    rng: &mut R,
) -> Result<Proof<F, PC>, Error<PC::Error>> {
    /*
        ADD YOUR CODE HERE
    */
    /*
    In the rest of protocol that is not described here, the masking polynomial is opened twice. Therefore, the masking polynomial cannot be a constant polynomial.
    */

    // any polynomial s(X) which has `s(0) = 0` will sum to 0 on H
    let s_vec = vec![F::zero(), F::one()];
    let s_poly = DensePolynomial::from_coefficients_vec(s_vec);

    let f_poly = f.polynomial();

    let lhs = f_poly + &s_poly;

    let (h_poly, x_gx) = lhs.divide_by_vanishing_poly(statement.domain).unwrap();
    let g_vec = x_gx.coeffs[1..].to_vec();
    let g_poly = DensePolynomial::from_coefficients_vec(g_vec);

    let s = LabeledPolynomial::new("s".into(), s_poly.clone(), None, None);
    let h = LabeledPolynomial::new("h".into(), h_poly.clone(), None, None);
    let g = LabeledPolynomial::new(
        "g".into(),
        g_poly.clone(),
        Some(statement.domain.size() - 2),
        None,
    );

    let (s_commitment, s_rand) = PC::commit(&ck, &[s.clone()], Some(rng)).unwrap();
    let (h_commitment, h_rand) = PC::commit(&ck, &[h.clone()], Some(rng)).unwrap();
    let (g_commitment, g_rand) = PC::commit(&ck, &[g.clone()], Some(rng)).unwrap();

    let mut fs_rng = FS::initialize(&to_bytes![&PROTOCOL_NAME, statement].unwrap());

    fs_rng.absorb(&to_bytes![s_commitment, h_commitment, g_commitment].unwrap());

    let xi = F::rand(&mut fs_rng);
    let opening_challenge = F::rand(&mut fs_rng);

    let pc_proof = {
        let point_label = String::from("xi");
        let query_set = QuerySet::from([
            ("f".into(), (point_label.clone(), xi)),
            ("h".into(), (point_label.clone(), xi)),
            ("g".into(), (point_label.clone(), xi)),
            ("s".into(), (point_label, xi)),
        ]);

        let polys = vec![f.clone(), s.clone(), h.clone(), g.clone()];

        let rands = vec![f_rand, &s_rand[0], &h_rand[0], &g_rand[0]];

        let f_comm = LabeledCommitment::new("f".into(), statement.f.clone(), None);
        let commitments = vec![f_comm, s_commitment[0].clone(), h_commitment[0].clone(), g_commitment[0].clone()];

        PC::batch_open(
            &ck,
            &polys,
            &commitments,
            &query_set,
            opening_challenge,
            rands,
            Some(rng),
        )
    };

    Ok(Proof {
        f_opening: f_poly.evaluate(&xi),
        s: s_commitment[0].commitment().clone(),
        s_opening: s_poly.evaluate(&xi),
        g: g_commitment[0].commitment().clone(),
        g_opening: g_poly.evaluate(&xi),
        h: h_commitment[0].commitment().clone(),
        h_opening: h_poly.evaluate(&xi),
        pc_proof: pc_proof.unwrap(),
    })
}

pub fn malicious_prover<
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    FS: FiatShamirRng,
    R: RngCore,
>(
    ck: &PC::CommitterKey,
    statement: &Statement<F, PC>,
    f: &LabeledPolynomial<F, DensePolynomial<F>>,
    f_rand: &PC::Randomness,
    rng: &mut R,
) -> Result<Proof<F, PC>, Error<PC::Error>> {
    /*
        ADD YOUR CODE HERE
    */
    /*
    In the rest of protocol that is not described here, the masking polynomial is opened twice. Therefore, the masking polynomial cannot be a constant polynomial.
    */

    // begin sanity
    let mut real_sum = F::zero();
    for h in statement.domain.elements() {
        real_sum += f.evaluate(&h);
    }
    // end sanity

    real_sum = F::zero() - real_sum;
    let card_inverse = statement.domain.size_as_field_element().inverse().unwrap();
    real_sum = real_sum * card_inverse;

    let s_vec = vec![real_sum, F::one()];
    let s_poly = DensePolynomial::from_coefficients_vec(s_vec);
    let f_poly = f.polynomial();

    let lhs = f_poly + &s_poly;

    let (h_poly, x_gx) = lhs.divide_by_vanishing_poly(statement.domain).unwrap();
    let g_vec = x_gx.coeffs[1..].to_vec();
    let g_poly = DensePolynomial::from_coefficients_vec(g_vec);

    let s = LabeledPolynomial::new("s".into(), s_poly.clone(), None, None);
    let h = LabeledPolynomial::new("h".into(), h_poly.clone(), None, None);
    let g = LabeledPolynomial::new(
        "g".into(),
        g_poly.clone(),
        Some(statement.domain.size() - 2),
        None,
    );

    let (s_commitment, s_rand) = PC::commit(&ck, &[s.clone()], Some(rng)).unwrap();
    let (h_commitment, h_rand) = PC::commit(&ck, &[h.clone()], Some(rng)).unwrap();
    let (g_commitment, g_rand) = PC::commit(&ck, &[g.clone()], Some(rng)).unwrap();

    let mut fs_rng = FS::initialize(&to_bytes![&PROTOCOL_NAME, statement].unwrap());

    fs_rng.absorb(&to_bytes![s_commitment, h_commitment, g_commitment].unwrap());

    let xi = F::rand(&mut fs_rng);
    let opening_challenge = F::rand(&mut fs_rng);

    let pc_proof = {
        let point_label = String::from("xi");
        let query_set = QuerySet::from([
            ("f".into(), (point_label.clone(), xi)),
            ("h".into(), (point_label.clone(), xi)),
            ("g".into(), (point_label.clone(), xi)),
            ("s".into(), (point_label, xi)),
        ]);

        let polys = vec![f.clone(), s.clone(), h.clone(), g.clone()];

        let rands = vec![f_rand, &s_rand[0], &h_rand[0], &g_rand[0]];

        let f_comm = LabeledCommitment::new("f".into(), statement.f.clone(), None);
        let commitments = vec![f_comm, s_commitment[0].clone(), h_commitment[0].clone(), g_commitment[0].clone()];

        PC::batch_open(
            &ck,
            &polys,
            &commitments,
            &query_set,
            opening_challenge,
            rands,
            Some(rng),
        )
    };

    Ok(Proof {
        f_opening: f_poly.evaluate(&xi),
        s: s_commitment[0].commitment().clone(),
        s_opening: s_poly.evaluate(&xi),
        g: g_commitment[0].commitment().clone(),
        g_opening: g_poly.evaluate(&xi),
        h: h_commitment[0].commitment().clone(),
        h_opening: h_poly.evaluate(&xi),
        pc_proof: pc_proof.unwrap(),
    })
}
