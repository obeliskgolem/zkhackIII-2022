use crate::pow_sp;
use ark_bls12_cheon::{Bls12Cheon, Fr, G1Projective as G1, G2Projective as G2}; //
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ff::Field;
use core::ops::Range;
use num_traits::One;
use rayon::prelude::*;
use std::collections::HashMap;
use std::ops::Mul;
use std::sync::Arc;
use crate::utils::bigInt_to_u128;


pub fn attack(P: G1, tau_P: G1, tau_d1_P: G1, Q: G2, tau_d2_Q: G2, d: u128, k0: u128, k1: u128) -> Fr {
    let two = Fr::one() + Fr::one();
    let tau_2 = pow_sp(two, k1, 126);

    // order = (q - 1) / d
    let order = 1587011986761171u128;
    let tau_2 = pow_sp(tau_2, order,126);

    let tau_1 = pow_sp(two, k0, 126);

    let tau = tau_1 * tau_2;

    tau
}

pub fn verify_k0(P: G1, tau_P: G1, tau_d1_P: G1, Q: G2, tau_d2_Q: G2, d: u128, k0: u128) {
    let mut gamma = Bls12Cheon::pairing(tau_d1_P, tau_d2_Q);

    let two = Fr::one() + Fr::one();
    let zeta = pow_sp(two, d, 64);

    let scalar = pow_sp(zeta, k0, 64);
    let p_k0 = P.mul(scalar);

    let mut k0_gt = Bls12Cheon::pairing(p_k0, Q);

    println!("k0_gt == alpha d: {}", k0_gt == gamma);
}

pub fn calc_k0(P: G1, tau_P: G1, tau_d1_P: G1, Q: G2, tau_d2_Q: G2, d: u128) -> u128 {
    let mut speedup_hash_table = Arc::new(dashmap::DashMap::<_, u128>::new());

    let two = Fr::one() + Fr::one();
    let zeta = pow_sp(two, d, 64);
    println!("zeta_1 = {}", zeta);

    // dd = sqrt((q-1) / d)
    let dd = 39837320;

    // since we know the most significant bits of k0 is 10111101110, we can modify the GSBS algorithm to shrink the search domain
    // let k0 = k' + d'v' + u', d' = 2^18, 0 <= u', v' < d'
    // we use [zeta^(-k') * alpha^d]P as the beta for computing DL
    // in this way we only need to search 2^18 + 2^18 times for u', v'
    // at last we can get d', v' and u', then we get k0
    let ddd = 1 << 18;
    let v_range = 0..ddd;
    let u_range = 0..ddd;

    let k0_most_sig: u128 = 15854 << 36;
    let scalar = pow_sp(zeta, k0_most_sig, 64);
    let scalar_inv = scalar.inverse().unwrap();

    println!("scalar * scalar_inv = {}", scalar * scalar_inv);

    let p_alpha_d_neg_k = tau_d1_P.mul(scalar_inv);

    let a_neg_m = pow_sp(zeta, ddd, 64);
    let a_neg_m = a_neg_m.inverse().unwrap();

    let n_thread = 6;
    let n_chunks = ddd / n_thread;

    let gt = Bls12Cheon::pairing(P, Q);

    // we don't have [alpha^d]P in G1, only have [alpha^d1]P, so we have to compare the results in GT, that means we need a pairing
    let gamma = Bls12Cheon::pairing(p_alpha_d_neg_k, tau_d2_Q);

    let mut handles = Vec::new();

    for thread_id in 0..n_thread {
        let seperate_hash_table = speedup_hash_table.clone();

        let handle = std::thread::spawn(move || {
            let start = thread_id * n_chunks;
            let end = std::cmp::min(ddd, (thread_id + 1) * n_chunks);
            for u in start..end {
                if u % 1024 == 0 {
                    println!("searching for u = {u}");
                }
                let scalar = pow_sp(zeta, u as u128, 64);

                // [zeta^u]*P
                let paired = gt * scalar;
                seperate_hash_table.insert(paired, u as u128);
            }
        });

        handles.push(handle);
    }

    for h in handles {
        h.join().unwrap();
    }

    let mut scalar = Fr::one();

    let mut kk = 0u128;

    for v in v_range {
        if v % 1024 == 0 {
            println!("searching for v = {v}");
        }

        let p = gamma * scalar;
        // let p = p_alpha_d_neg_k.mul(scalar);
        // let gamma = Bls12Cheon::pairing(p, tau_d2_Q);

        let result = (*speedup_hash_table).get(&p);

        if result.is_none() {
            scalar = scalar * a_neg_m;
            continue;
        };

        let u = *result.unwrap();

        kk = ddd * v + u;
        println!("v = {v}, u = {u}, k = {kk}, ddd = {ddd}");
        break;
    }

    kk + k0_most_sig
}

pub fn calc_k1(P: G1, tau_P: G1, tau_d1_P: G1, Q: G2, tau_d2_Q: G2, d: u128, k0: u128) -> u128 {
    let mut speedup_hash_table = Arc::new(dashmap::DashMap::<_, u128>::new());

    // order = (q-1)/d
    let order = 1587011986761171u128;
    let two = Fr::one() + Fr::one();
    let zeta = pow_sp(two, order, 126);
    println!("zeta = {}", zeta);

    // ddd = sqrt(d)
    let ddd = 26497;
    let v_range = 0..ddd;
    let u_range = 0..ddd;

    let scalar = pow_sp(two, k0, 64);
    let scalar_inv = scalar.inverse().unwrap();

    println!("scalar * scalar_inv = {}", scalar * scalar_inv);

    let p_alpha_d_neg_k = tau_P.mul(scalar_inv);

    let a_neg_m = pow_sp(zeta, ddd, 64);
    let a_neg_m = a_neg_m.inverse().unwrap();

    let n_thread = 6;
    let n_chunks = ddd / n_thread;

    // actually we need no pairing here, we can compare the results in G1
    // but it's convinient to use existing codes :)
    let gt = Bls12Cheon::pairing(P, Q);
    let new_gt = Bls12Cheon::pairing(p_alpha_d_neg_k, Q);

    let mut handles = Vec::new();

    for thread_id in 0..n_thread {
        let seperate_hash_table = speedup_hash_table.clone();

        let handle = std::thread::spawn(move || {
            let start = thread_id * n_chunks;
            let end = std::cmp::min(ddd, (thread_id + 1) * n_chunks);
            for u in start..end {
                if u % 1024 == 0 {
                    println!("searching for u = {u}");
                }
                let scalar = pow_sp(zeta, u as u128, 64);
                let scalar_inv = scalar.inverse().unwrap();

                // [zeta^u]*P
                let paired = new_gt * scalar_inv;
                seperate_hash_table.insert(paired, u as u128);
            }
        });

        handles.push(handle);
    }

    for h in handles {
        h.join().unwrap();
    }

    let mut scalar = Fr::one();
    let mut gamma = gt * scalar;

    let mut k1 = 0u128;

    for v in v_range {
        if v % 1024 == 0 {
            println!("searching for v = {v}");
        }

        let scalar = pow_sp(zeta, ddd * v, 126);
        let p = gt * scalar;

        let result = (*speedup_hash_table).get(&p);

        if result.is_none() {
            continue;
        };

        let u = *result.unwrap();

        k1 = ddd * v + u;
        println!("v = {v}, u = {u}, k = {k1}, ddd = {ddd}");
        break;
    }

    k1
}
