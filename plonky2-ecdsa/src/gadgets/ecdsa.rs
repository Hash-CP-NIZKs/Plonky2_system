use core::marker::PhantomData;

use plonky2::field::extension::Extendable;
use plonky2::field::secp256k1_scalar::Secp256K1Scalar;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::witness::PartialWitness;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

use crate::curve::curve_types::{Curve, CurveScalar};
use crate::curve::ecdsa::{sign_message, ECDSAPublicKey, ECDSASecretKey, ECDSASignature};
use crate::curve::secp256k1::Secp256K1;
use crate::gadgets::curve::{AffinePointTarget, CircuitBuilderCurve};
use crate::gadgets::curve_fixed_base::fixed_base_curve_mul_circuit;
use crate::gadgets::glv::CircuitBuilderGlv;
use crate::gadgets::nonnative::{CircuitBuilderNonNative, NonNativeTarget};

#[derive(Clone, Debug)]
pub struct ECDSASecretKeyTarget<C: Curve>(pub NonNativeTarget<C::ScalarField>);

#[derive(Clone, Debug)]
pub struct ECDSAPublicKeyTarget<C: Curve>(pub AffinePointTarget<C>);

#[derive(Clone, Debug)]
pub struct ECDSASignatureTarget<C: Curve> {
    pub r: NonNativeTarget<C::ScalarField>,
    pub s: NonNativeTarget<C::ScalarField>,
}

pub fn verify_message_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    msg: NonNativeTarget<Secp256K1Scalar>,
    sig: ECDSASignatureTarget<Secp256K1>,
    pk: ECDSAPublicKeyTarget<Secp256K1>,
) {
    let ECDSASignatureTarget { r, s } = sig;

    builder.curve_assert_valid(&pk.0);

    let c = builder.inv_nonnative(&s);
    let u1 = builder.mul_nonnative(&msg, &c);
    let u2 = builder.mul_nonnative(&r, &c);

    let point1 = fixed_base_curve_mul_circuit(builder, Secp256K1::GENERATOR_AFFINE, &u1);
    let point2 = builder.glv_mul(&pk.0, &u2);
    let point = builder.curve_add(&point1, &point2);

    let x = NonNativeTarget::<Secp256K1Scalar> {
        value: point.x.value,
        _phantom: PhantomData,
    };
    builder.connect_nonnative(&r, &x);
}



#[cfg(test)]
mod tests {
    // extern crate num_bigint;
    // extern crate num_integer;
    // extern crate num_traits;
    // extern crate rand;

    use anyhow::Ok;
    use itertools::Itertools;
    use num_bigint::BigUint;
    use num_bigint::RandBigInt;
    use num_traits::{One, ToPrimitive, Zero};
    
    use plonky2::field::secp256k1_base::Secp256K1Base;
    use plonky2::field::types::PrimeField;
    use plonky2::fri::reduction_strategies::FriReductionStrategy;
    use plonky2::fri::FriConfig;
    use plonky2::gadgets::lookup::U16RANGECHECK;
    use plonky2::gates::lookup_table::LookupTable;
    use plonky2::plonk::circuit_data::CommonCircuitData;
    use plonky2::plonk::circuit_data::VerifierOnlyCircuitData;
    use plonky2::plonk::config::AlgebraicHasher;
    use plonky2::plonk::config::KeccakGoldilocksConfig;
    use plonky2::plonk::proof::ProofWithPublicInputs;
    use plonky2_maybe_rayon::IndexedParallelIterator;
    use plonky2_maybe_rayon::MaybeIntoParIter;
    use plonky2_maybe_rayon::MaybeParIterMut;
    use plonky2_maybe_rayon::ParallelIterator;
    use plonky2_u32::gadgets::range_check::range_check_u32_circuit;
    use plonky2_u32::witness::WitnessU32;
    use std::cmp::max;

    use core::hash::BuildHasher;
    use std::sync::Arc;
    use std::time::Instant;

    use anyhow::Result;
    use itertools::Product;

    use num::PrimInt;
    
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::field::types::Field;
    use plonky2::field::types::PrimeField64;
    use plonky2::field::types::Sample;
    use plonky2::gates::poseidon::PoseidonGate;
    use plonky2::hash::hash_types::HashOutTarget;
    use plonky2::hash::poseidon::PoseidonHash;
    use plonky2::iop::target;
    use plonky2::iop::target::BoolTarget;
    use plonky2::iop::target::Target;
    use plonky2::iop::witness::{PartialWitness, WitnessWrite};
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use serde::de::Expected;

    use super::*;
    use crate::curve::curve_types::CurveScalar;
    use crate::curve::ecdsa::{sign_message, ECDSAPublicKey, ECDSASecretKey, ECDSASignature};
    use crate::curve::secp256k1;
    use rand::Rng;

   
     #[test]
    fn test_dl1_worst_case() -> Result<()> {

        // test the prover time of Plonky2 for dl_1 for worst case
        // To prove one scalar multiplications, need a number of 512 point additions at worst.
     

        const D: usize = 2;
        type C = KeccakGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type Hasher = PoseidonHash;
        type Curve = Secp256K1;
        
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_ecc_config());

        let rng = rand::thread_rng();

        let mut points = Vec::new();
 
        for _ in 0..512 {
         
            let x1 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, x1.value.limbs.clone());
            let y1 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, y1.value.limbs.clone());

            let x2 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, x2.value.limbs.clone());
            let y2 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, y2.value.limbs.clone());

            let point1 = AffinePointTarget::<Curve> {
                x: x1.clone(),
                y: y1.clone(),
            };

            let point2 = AffinePointTarget::<Curve> {
                x: x2.clone(),
                y: y2.clone(),
            };

            points.push((point1, point2));
        }

      
        for (point1, point2) in points.iter() {
            builder.curve_add(point1, point2);
        }

        let mut rand_points = Vec::new();

        for _ in 0..512 {
            let x1r = Secp256K1Base::rand();
            let y1r = Secp256K1Base::rand();
            let x2r = Secp256K1Base::rand();
            let y2r = Secp256K1Base::rand();
            rand_points.push((x1r, y1r, x2r, y2r));
        }
        let mut pw = PartialWitness::new();
        // set partial witnesses
        for (i, (x1r, y1r, x2r, y2r)) in rand_points.iter().enumerate() {
            for (j, limb) in x1r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].0.x.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].0.x.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }

            for (j, limb) in y1r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].0.y.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].0.y.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }

            for (j, limb) in x2r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].1.x.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].1.x.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }

            for (j, limb) in y2r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].1.y.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].1.y.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }
        }
        // let point = builder.curve_add(&point1, &point2);

        // let x = NonNativeTarget::<Secp256K1Scalar> {
        //     value: point.x.value,
        //     _phantom: PhantomData,
        // };
        // builder.connect_nonnative(&r_target, &x);
        builder.print_gate_counts(0);
        dbg!(builder.num_gates());
        let data = builder.build::<C>();
        println!("circuit degree {:?}", data.common.fri_params);
        // println!("circuit numpatial {:?}",data.common.num_partial_products);
        // println!("circuit gates {:?}",data.common.gates);

        println!("circuit lde_size {:?}", data.common.lde_size());
        
        let start_time = Instant::now();
        let proof = data.prove(pw).unwrap();
        let elapsed_time = start_time.elapsed();
        println!("generate proof {:?}", elapsed_time);

        let proof_size_in_bytes = proof.to_bytes().len();
        println!("Serialized proof size: {} bytes", proof_size_in_bytes);
        let start_time = Instant::now();
        data.verify(proof.clone());
        let elapsed_time = start_time.elapsed();
        println!("verify proof {:?}", elapsed_time);
       
        Ok(())
    }

    #[test]
    fn test_dl1_average_case() -> Result<()> {

        // test the prover time of Plonky2 for dl_1 for average case
        // To prove one scalar multiplications, need a number of 256 point additions in average.
     

        const D: usize = 2;
        type C = KeccakGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type Hasher = PoseidonHash;
        type Curve = Secp256K1;
        
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_ecc_config());

        let rng = rand::thread_rng();

        let mut points = Vec::new();
 
        for _ in 0..256 {
         
            let x1 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, x1.value.limbs.clone());
            let y1 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, y1.value.limbs.clone());

            let x2 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, x2.value.limbs.clone());
            let y2 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, y2.value.limbs.clone());

            let point1 = AffinePointTarget::<Curve> {
                x: x1.clone(),
                y: y1.clone(),
            };

            let point2 = AffinePointTarget::<Curve> {
                x: x2.clone(),
                y: y2.clone(),
            };

            points.push((point1, point2));
        }

      
        for (point1, point2) in points.iter() {
            builder.curve_add(point1, point2);
        }

        let mut rand_points = Vec::new();

        for _ in 0..256 {
            let x1r = Secp256K1Base::rand();
            let y1r = Secp256K1Base::rand();
            let x2r = Secp256K1Base::rand();
            let y2r = Secp256K1Base::rand();
            rand_points.push((x1r, y1r, x2r, y2r));
        }
        let mut pw = PartialWitness::new();
        // set partial witnesses
        for (i, (x1r, y1r, x2r, y2r)) in rand_points.iter().enumerate() {
            for (j, limb) in x1r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].0.x.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].0.x.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }

            for (j, limb) in y1r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].0.y.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].0.y.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }

            for (j, limb) in x2r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].1.x.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].1.x.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }

            for (j, limb) in y2r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].1.y.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].1.y.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }
        }
        // let point = builder.curve_add(&point1, &point2);

        // let x = NonNativeTarget::<Secp256K1Scalar> {
        //     value: point.x.value,
        //     _phantom: PhantomData,
        // };
        // builder.connect_nonnative(&r_target, &x);
        builder.print_gate_counts(0);
        dbg!(builder.num_gates());
        let data = builder.build::<C>();
        println!("circuit degree {:?}", data.common.fri_params);
        // println!("circuit numpatial {:?}",data.common.num_partial_products);
        // println!("circuit gates {:?}",data.common.gates);

        println!("circuit lde_size {:?}", data.common.lde_size());
        
        let start_time = Instant::now();
        let proof = data.prove(pw).unwrap();
        let elapsed_time = start_time.elapsed();
        println!("generate proof {:?}", elapsed_time);

        let proof_size_in_bytes = proof.to_bytes().len();
        println!("Serialized proof size: {} bytes", proof_size_in_bytes);
        let start_time = Instant::now();
        data.verify(proof.clone());
        let elapsed_time = start_time.elapsed();
        println!("verify proof {:?}", elapsed_time);
       
        Ok(())
    }

   

 #[test]
    fn test_dl1_sigma_aok() -> Result<()> {

        // test the prover time of Plonky2 for dl_1 using our proposed sigma aok.
        // this involves 41 elliptic curve point additions, 
        // 3 point doublings, 32 non-native multiplications and a Poseidon hash of 66 elements.

        fn get_predefined_prime() -> BigUint {
            BigUint::parse_bytes(
                b"115792089237316195423570985008687907853269984665640564039457584007913129639937",
                10,
            )
            .unwrap()
        }
        
        fn generate_random_256bit_u32() -> Vec<u32> {
            let mut rng = rand::thread_rng();
            let mut result = Vec::new();
            for _ in 0..8 {
                result.push(rng.gen::<u32>());
            }
            result
        }
        fn generate_random_512bit_u32() -> Vec<u32> {
            let mut rng = rand::thread_rng();
            let mut result = Vec::new();
            for _ in 0..16 {
                result.push(rng.gen::<u32>());
            }
            result
        }
      
        fn generate_random_4bit_u64() -> u64 {
            let mut rng = rand::thread_rng();
            let mut result = rng.gen_range(0..16) as u64;

            result
        }
        const D: usize = 2;
        type C = KeccakGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type Hasher = PoseidonHash;
        type Curve = Secp256K1;
        
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_ecc_config());

        let rng = rand::thread_rng();

        const NUM_INSTANCES: usize = 32;//(parallet times)
        const LIMB_SIZE: u64 = 1 << 32;

        //k+e*lamda
        let mut k = Vec::new();
        let mut e = Vec::new();

        for _ in 0..NUM_INSTANCES {
            k.push(builder.add_virtual_targets(8));
            e.push(builder.add_virtual_target());
        }

        let lambda = builder.add_virtual_targets(8);

        let mut final_results = Vec::new();

        for i in 0..NUM_INSTANCES {
            let mut final_result_v = lambda.clone();

            for j in 0..final_result_v.len() {
                final_result_v[j] = builder.mul(final_result_v[j], e[i]);
            }

            for (j, &ki) in k[i].iter().enumerate() {
                final_result_v[j] = builder.add(final_result_v[j], ki);
            }

            final_results.push(final_result_v);
        }

        let k_real: Vec<Vec<u32>> = (0..NUM_INSTANCES)
            .map(|_| generate_random_256bit_u32())
            .collect();
        let e_real: Vec<u64> = (0..NUM_INSTANCES)
            .map(|_| generate_random_4bit_u64())
            .collect();
        let lambda_real: Vec<u32> = generate_random_256bit_u32();

        let q_original = get_predefined_prime();

        let mut results_real = Vec::new();

        for i in 0..NUM_INSTANCES {
            let mut final_result_real = Vec::new();
            for j in 0..k_real[i].len() {
                final_result_real.push((lambda_real[j] as u64 * e_real[i]) + k_real[i][j] as u64);
            }

            let base: u64 = 1 << 32;
            let mut carries_fresult = Vec::new();
            let mut limbs_fresult = Vec::new();

            for i in 0..final_result_real.len() {
        
                if i == 0 {
                    carries_fresult.push(final_result_real[i] / base);
                    limbs_fresult.push(final_result_real[i] % base);
                } else if i >= 1 && i < final_result_real.len() {
                    carries_fresult.push((final_result_real[i] + carries_fresult[i - 1]) / base);
                    limbs_fresult.push((final_result_real[i] + carries_fresult[i - 1]) % base);
                }
            }

            while carries_fresult[carries_fresult.len() - 1] > 0 {
                limbs_fresult.push(carries_fresult[carries_fresult.len() - 1] % base);
                carries_fresult.push(carries_fresult[carries_fresult.len() - 1] / base);
            }

            let mut final_result_int = BigUint::zero();
            for (i, &limb) in final_result_real.iter().enumerate() {
                final_result_int += BigUint::from(limb) << (32 * i);
            }

            let p = final_result_int.clone() / &q_original;
            let r = final_result_int.clone() % &q_original;
            assert_eq!(p.clone() * &q_original + r.clone(), final_result_int);

            let mut p_limbs = Vec::new();
            let mut r_limbs = Vec::new();
            let mut q_limbs = Vec::new();

            let mut temp_p = p.clone();
            let mut temp_r = r.clone();
            let mut temp_q = q_original.clone();

            while temp_p > BigUint::zero() {
                p_limbs.push((&temp_p % BigUint::from(base)).to_u64().unwrap());
                temp_p = temp_p / BigUint::from(base);
            }

            while temp_r > BigUint::zero() {
                r_limbs.push((&temp_r % BigUint::from(base)).to_u64().unwrap());
                temp_r = temp_r / BigUint::from(base);
            }

            while temp_q > BigUint::zero() {
                q_limbs.push((&temp_q % BigUint::from(base)).to_u64().unwrap());
                temp_q = temp_q / BigUint::from(base);
            }
            let max_len_pqr = p_limbs.len() + q_limbs.len() - 1;

            let mut max_len = 0;

            if p_limbs.len() != 0 {
                max_len = std::cmp::max(max_len_pqr, r_limbs.len());
            } else if p_limbs.len() == 0 {
                max_len = r_limbs.len();
            }

            let mut product_pqr = vec![0u64; max_len];
            for j in 0..p_limbs.len() {
                for k in 0..q_limbs.len() {
                    product_pqr[j + k] += p_limbs[j] * q_limbs[k];
                }
            }
            for j in 0..r_limbs.len() {
                product_pqr[j] += r_limbs[j];
            }

            let mut carries_z = Vec::new();
            let mut limbs_z = Vec::new();
            for i in 0..product_pqr.len() {
             
                if i == 0 {
                    carries_z.push(product_pqr[i] / base);
                    limbs_z.push(product_pqr[i] % base);
                } else if i >= 1 && i < product_pqr.len() {
                    carries_z.push((product_pqr[i] + carries_z[i - 1]) / base);
                    limbs_z.push((product_pqr[i] + carries_z[i - 1]) % base);
                }
            }

            while carries_z[carries_z.len() - 1] > 0 {
                limbs_z.push(carries_z[carries_z.len() - 1] % base);
                carries_z.push(carries_z[carries_z.len() - 1] / base);
            }

            results_real.push((
                carries_fresult,
                limbs_fresult,
                carries_z,
                limbs_z,
                p_limbs,
                q_limbs,
                r_limbs,
            ));
        }

        let mut q_v = Vec::new();
        let mut carries_fresult_v = Vec::new();
        let mut limbs_fresult_v = Vec::new();
        let mut carries_z_v = Vec::new();
        let mut limbs_z_v = Vec::new();
        let mut p_v = Vec::new();
        let mut reminder_v = Vec::new();

        for i in 0..NUM_INSTANCES {
            let (carries_fresult, limbs_fresult, carries_z, limbs_z, p_limbs, q_limbs, r_limbs) =
                &results_real[i];
            q_v.push(builder.add_virtual_targets(q_limbs.len()));
            carries_fresult_v.push(builder.add_virtual_targets(carries_fresult.len()));
            limbs_fresult_v.push(builder.add_virtual_targets(limbs_fresult.len()));
            carries_z_v.push(builder.add_virtual_targets(carries_z.len()));
            limbs_z_v.push(builder.add_virtual_targets(limbs_z.len()));
            p_v.push(builder.add_virtual_targets(p_limbs.len()));
            reminder_v.push(builder.add_virtual_targets(r_limbs.len()));
        }
        let mut final_result_modq_all = Vec::new();
        let mut fz_modq_all = Vec::new();
        for j in 0..NUM_INSTANCES {
            for i in 0..carries_fresult_v[j].len() {
                let mut final_result_modq = Vec::new();
                if i == 0 {
                    let carryshifted = builder
                        .mul_const(F::from_canonical_u64(LIMB_SIZE), carries_fresult_v[j][0]);
                    let expected_result = builder.add(carryshifted, limbs_fresult_v[j][0]);
                    builder.is_equal(final_results[j][0], expected_result);
                    final_result_modq.push(limbs_fresult_v[j][0]);
                } else if i >= 1 && i < final_results[j].len() {
                    let carryshifted = builder
                        .mul_const(F::from_canonical_u64(LIMB_SIZE), carries_fresult_v[j][i]);
                    let expected_result = builder.add(carryshifted, limbs_fresult_v[j][i]);
                    let new_carry = builder.add(final_results[j][i], carries_fresult_v[j][i - 1]);
                    builder.is_equal(new_carry, expected_result);
                    final_result_modq.push(limbs_fresult_v[j][i]);
                } else if i >= final_results[j].len() && i < carries_fresult_v[j].len() {
                    let carryshifted = builder
                        .mul_const(F::from_canonical_u64(LIMB_SIZE), carries_fresult_v[j][i]);
                    let expected_result = builder.add(carryshifted, limbs_fresult_v[j][i]);
                    builder.is_equal(carries_fresult_v[j][i - 1], expected_result);
                    final_result_modq.push(limbs_fresult_v[j][i]);
                }
                final_result_modq_all.push(final_result_modq);
            }

            let max_len_pqr = p_v[j].len() + q_v[j].len() - 1;
            let max_len = std::cmp::max(max_len_pqr, reminder_v[j].len());
            let mut t = vec![builder.zero(); max_len];

            for i in 0..q_v[j].len() {
                for k in 0..p_v[j].len() {
                    let term = builder.mul(q_v[j][i], p_v[j][k]);
                    t[i + k] = builder.add(term, t[i + k]);
                }
            }

            for i in 0..reminder_v[j].len() {
                t[i] = builder.add(t[i], reminder_v[j][i]);
            }

            for i in 0..carries_z_v[j].len() {
                let mut fz_modq = Vec::new();
                if i == 0 {
                    let carryshifted =
                        builder.mul_const(F::from_canonical_u64(LIMB_SIZE), carries_z_v[j][0]);
                    let expected_result = builder.add(carryshifted, limbs_z_v[j][0]);
                    builder.is_equal(t[0], expected_result);
                    fz_modq.push(limbs_z_v[j][0]);
                } else if i >= 1 && i < t.len() {
                    let carryshifted =
                        builder.mul_const(F::from_canonical_u64(LIMB_SIZE), carries_z_v[j][i]);
                    let expected_result = builder.add(carryshifted, limbs_z_v[j][i]);
                    let new_carry = builder.add(t[i], carries_z_v[j][i - 1]);
                    builder.is_equal(new_carry, expected_result);
                    fz_modq.push(limbs_z_v[j][i]);
                } else if i >= t.len() && i < carries_z_v[j].len() {
                    let carryshifted =
                        builder.mul_const(F::from_canonical_u64(LIMB_SIZE), carries_z_v[j][i]);
                    let expected_result = builder.add(carryshifted, limbs_z_v[j][i]);
                    builder.is_equal(carries_z_v[j][i - 1], expected_result);
                    fz_modq.push(limbs_z_v[j][i]);
                }
                fz_modq_all.push(fz_modq);
            }

            for i in 0..reminder_v[j].len() {
                builder.register_public_input(reminder_v[j][i]);
            }
        }

        for j in 0..NUM_INSTANCES {
            assert!(final_result_modq_all[j].len() == fz_modq_all[j].len());

            for i in 0..final_result_modq_all[j].len() {
                builder.is_equal(final_result_modq_all[j][i], fz_modq_all[j][i]);
            }
        }
        let mut pw = PartialWitness::new();

        // hash(A,k,r)
        
        let mut masking = builder.add_virtual_targets(16);
        println!("masking_len{}", masking.len());
        let masking_real = generate_random_512bit_u32();

        let mut hashA = Vec::new();
        let mut hashA_real = Vec::new();
        for i in 0..k.len(){
            hashA.push(builder.add_virtual_targets(16));
            hashA_real.push(generate_random_512bit_u32());
       
        }
        for i in 0..hashA.len() {
            builder.hash_n_to_hash_no_pad::<Hasher>(hashA[i].clone());
            for j in 0..hashA[i].len() {
                pw.set_target(
                    hashA[i][j],
                    GoldilocksField::from_canonical_u64(hashA_real[i][j] as u64),
                );
            }
        }
        masking.extend(lambda.clone());

        builder.hash_n_to_hash_no_pad::<Hasher>(masking.clone());

        let mut ktargets: Vec<Target> = Vec::new();
        for i in 0..k.len() {
            for j in 0..k[i].len() {
                ktargets.push(k[i][j]);
            }
        }

        builder.hash_n_to_hash_no_pad::<Hasher>(ktargets);

        for i in 0..masking.len() - 8 {
            pw.set_target(
                masking[i],
                GoldilocksField::from_canonical_u64(masking_real[i] as u64),
            );
        }
        let u16range = U16RANGECHECK.to_vec();
        let table: LookupTable = Arc::new((0..=65535).zip_eq(u16range).collect());
        let u16range = builder.add_lookup_table_from_pairs(table);
        
        
        for i in 0..NUM_INSTANCES {
            let (carries_fresult, limbs_fresult, carries_z, limbs_z, p_limbs, q_limbs, r_limbs) =
                &results_real[i];

            for j in 0..reminder_v[i].len() {
                let a = builder.add_virtual_target();
                let b = builder.add_virtual_target();
                let c =builder.mul_const_add(F::from_canonical_u64(1<<16), b, a);
                builder.is_equal(c, reminder_v[i][j]);
                builder.add_lookup_from_index(a, u16range);
                builder.add_lookup_from_index(b, u16range);

                pw.set_target(reminder_v[i][j],GoldilocksField::from_canonical_u64(r_limbs[j] as u64));
                pw.set_target(b, GoldilocksField::from_canonical_u64(r_limbs[j]/(1<<16) as u64));
                pw.set_target(a, GoldilocksField::from_canonical_u64(r_limbs[j]%(1<<16) as u64));
            }
    
            for j in 0..p_v[i].len() {
                let a = builder.add_virtual_target();
                let b = builder.add_virtual_target();
                let c =builder.mul_const_add(F::from_canonical_u64(1<<16), b, a);
                builder.is_equal(c, p_v[i][j]);
                builder.add_lookup_from_index(a, u16range);
                builder.add_lookup_from_index(b, u16range);

                pw.set_target(p_v[i][j],GoldilocksField::from_canonical_u64(p_limbs[j] as u64));
                pw.set_target(b, GoldilocksField::from_canonical_u64(p_limbs[j]/(1<<16) as u64));
                pw.set_target(a, GoldilocksField::from_canonical_u64(p_limbs[j]%(1<<16) as u64));
            }

            for j in 0..limbs_z_v[i].len() {
                let a = builder.add_virtual_target();
                let b = builder.add_virtual_target();
                let c =builder.mul_const_add(F::from_canonical_u64(1<<16), b, a);
                builder.is_equal(c, limbs_z_v[i][j]);
                builder.add_lookup_from_index(a, u16range);
                builder.add_lookup_from_index(b, u16range);

                pw.set_target(limbs_z_v[i][j],GoldilocksField::from_canonical_u64(limbs_z[j] as u64));
                pw.set_target(b, GoldilocksField::from_canonical_u64(limbs_z[j]/(1<<16) as u64));
                pw.set_target(a, GoldilocksField::from_canonical_u64(limbs_z[j]%(1<<16) as u64));
            }

        
            for j in 0..limbs_fresult_v[i].len() {
                let a = builder.add_virtual_target();
                let b = builder.add_virtual_target();
                let c =builder.mul_const_add(F::from_canonical_u64(1<<16), b, a);
                builder.is_equal(c, limbs_fresult_v[i][j]);
                builder.add_lookup_from_index(a, u16range);
                builder.add_lookup_from_index(b, u16range);

                pw.set_target(limbs_fresult_v[i][j],GoldilocksField::from_canonical_u64(limbs_fresult[j] as u64));
                pw.set_target(b, GoldilocksField::from_canonical_u64(limbs_fresult[j]/(1<<16) as u64));
                pw.set_target(a, GoldilocksField::from_canonical_u64(limbs_fresult[j]%(1<<16) as u64));
            }

         

            for j in 0..q_v[i].len() {
     
                let a = builder.add_virtual_target();
                let b = builder.add_virtual_target();
                let c =builder.mul_const_add(F::from_canonical_u64(1<<16), b, a);
                builder.is_equal(c, q_v[i][j]);
                builder.add_lookup_from_index(a, u16range);
                builder.add_lookup_from_index(b, u16range);

                pw.set_target(q_v[i][j],GoldilocksField::from_canonical_u64(q_limbs[j] as u64));
                pw.set_target(b, GoldilocksField::from_canonical_u64(q_limbs[j]/(1<<16) as u64));
                pw.set_target(a, GoldilocksField::from_canonical_u64(q_limbs[j]%(1<<16) as u64));
              
            }

        
            for j in 0..k[i].len() {
     
                let a = builder.add_virtual_target();
                let b = builder.add_virtual_target();
                let c =builder.mul_const_add(F::from_canonical_u64(1<<16), b, a);
                builder.is_equal(c, k[i][j]);
                builder.add_lookup_from_index(a, u16range);
                builder.add_lookup_from_index(b, u16range);

                pw.set_target(k[i][j],GoldilocksField::from_canonical_u64(k_real[i][j] as u64));
                pw.set_target(b, GoldilocksField::from_canonical_u64((k_real[i][j]/(1<<16)) as u64));
                pw.set_target(a, GoldilocksField::from_canonical_u64((k_real[i][j]%(1<<16)) as u64));
              
            }

            builder.range_check(e[i], 4);

         
          

            for j in 0..carries_z_v[i].len() {
                pw.set_target(
                    carries_z_v[i][j],
                    GoldilocksField::from_canonical_u64(carries_z[j] as u64),
                );
            }

            
            for j in 0..carries_fresult_v[i].len() {
                pw.set_target(
                    carries_fresult_v[i][j],
                    GoldilocksField::from_canonical_u64(carries_fresult[j] as u64),
                );
            }

         

            pw.set_target(e[i], GoldilocksField::from_canonical_u64(e_real[i] as u64));
        }
        
      
        for j in 0..lambda.len() {
            let a = builder.add_virtual_target();
            let b = builder.add_virtual_target();
            let c =builder.mul_const_add(F::from_canonical_u64(1<<16), b, a);
            builder.is_equal(c, lambda[j]);
            builder.add_lookup_from_index(a, u16range);
            builder.add_lookup_from_index(b, u16range);

            pw.set_target(lambda[j],GoldilocksField::from_canonical_u64(lambda_real[j] as u64));
            pw.set_target(b, GoldilocksField::from_canonical_u64((lambda_real[j]/(1<<16)) as u64));
            pw.set_target(a, GoldilocksField::from_canonical_u64((lambda_real[j]%(1<<16)) as u64));
            
        }
      
        let mut points = Vec::new();

        for _ in 0..44 {
         
            let x1 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, x1.value.limbs.clone());
            let y1 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, y1.value.limbs.clone());

            let x2 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, x2.value.limbs.clone());
            let y2 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, y2.value.limbs.clone());

            let point1 = AffinePointTarget::<Curve> {
                x: x1.clone(),
                y: y1.clone(),
            };

            let point2 = AffinePointTarget::<Curve> {
                x: x2.clone(),
                y: y2.clone(),
            };

            points.push((point1, point2));
        }

      
        for (point1, point2) in points.iter() {
            builder.curve_add(point1, point2);
        }

        let mut rand_points = Vec::new();

        for _ in 0..44 {
            let x1r = Secp256K1Base::rand();
            let y1r = Secp256K1Base::rand();
            let x2r = Secp256K1Base::rand();
            let y2r = Secp256K1Base::rand();
            rand_points.push((x1r, y1r, x2r, y2r));
        }

        // set partial witnesses
        for (i, (x1r, y1r, x2r, y2r)) in rand_points.iter().enumerate() {
            for (j, limb) in x1r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].0.x.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].0.x.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }

            for (j, limb) in y1r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].0.y.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].0.y.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }

            for (j, limb) in x2r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].1.x.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].1.x.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }

            for (j, limb) in y2r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].1.y.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].1.y.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }
        }
        // let point = builder.curve_add(&point1, &point2);

        // let x = NonNativeTarget::<Secp256K1Scalar> {
        //     value: point.x.value,
        //     _phantom: PhantomData,
        // };
        // builder.connect_nonnative(&r_target, &x);
        builder.print_gate_counts(0);
        dbg!(builder.num_gates());
        let data = builder.build::<C>();
        println!("circuit degree {:?}", data.common.fri_params);
        // println!("circuit numpatial {:?}",data.common.num_partial_products);
        // println!("circuit gates {:?}",data.common.gates);

        println!("circuit lde_size {:?}", data.common.lde_size());
        
        let start_time = Instant::now();
        let proof = data.prove(pw).unwrap();
        let elapsed_time = start_time.elapsed();
        println!("generate proof {:?}", elapsed_time);

        let proof_size_in_bytes = proof.to_bytes().len();
        println!("Serialized proof size: {} bytes", proof_size_in_bytes);
        let start_time = Instant::now();
        data.verify(proof.clone());
        let elapsed_time = start_time.elapsed();
        println!("verify proof {:?}", elapsed_time);
       

        Ok(())
    }

   

   
    #[test]
    fn test_dl2_sigma_aok() -> Result<()> {

        // test the prover time of Plonky2 for dl_2 using our proposed sigma aok
        // this involves 82 point additions, 6 point doublings and 66 poseidon hashes.
     

        const D: usize = 2;
        type C = KeccakGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type Hasher = PoseidonHash;
        type Curve = Secp256K1;
        
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_ecc_config());

        let rng = rand::thread_rng();

        let mut points = Vec::new();
 
        for _ in 0..88 {
         
            let x1 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, x1.value.limbs.clone());
            let y1 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, y1.value.limbs.clone());

            let x2 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, x2.value.limbs.clone());
            let y2 = builder.add_virtual_nonnative_target::<Secp256K1Base>();
            range_check_u32_circuit(&mut builder, y2.value.limbs.clone());

            let point1 = AffinePointTarget::<Curve> {
                x: x1.clone(),
                y: y1.clone(),
            };

            let point2 = AffinePointTarget::<Curve> {
                x: x2.clone(),
                y: y2.clone(),
            };

            points.push((point1, point2));
        }

      
        for (point1, point2) in points.iter() {
            builder.curve_add(point1, point2);
        }

        let mut rand_points = Vec::new();

        for _ in 0..88 {
            let x1r = Secp256K1Base::rand();
            let y1r = Secp256K1Base::rand();
            let x2r = Secp256K1Base::rand();
            let y2r = Secp256K1Base::rand();
            rand_points.push((x1r, y1r, x2r, y2r));
        }
        let mut pw = PartialWitness::new();
        // set partial witnesses
        for (i, (x1r, y1r, x2r, y2r)) in rand_points.iter().enumerate() {
            for (j, limb) in x1r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].0.x.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].0.x.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }

            for (j, limb) in y1r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].0.y.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].0.y.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }

            for (j, limb) in x2r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].1.x.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].1.x.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }

            for (j, limb) in y2r.0.iter().enumerate() {
                pw.set_u32_target(
                    points[i].1.y.value.limbs[2 * j],
                    (*limb & 0xFFFFFFFF) as u32,
                );
                pw.set_u32_target(points[i].1.y.value.limbs[2 * j + 1], (*limb >> 32) as u32);
            }
        }
        // let point = builder.curve_add(&point1, &point2);

        // let x = NonNativeTarget::<Secp256K1Scalar> {
        //     value: point.x.value,
        //     _phantom: PhantomData,
        // };
        // builder.connect_nonnative(&r_target, &x);
        builder.print_gate_counts(0);
        dbg!(builder.num_gates());
        let data = builder.build::<C>();
        println!("circuit degree {:?}", data.common.fri_params);
        // println!("circuit numpatial {:?}",data.common.num_partial_products);
        // println!("circuit gates {:?}",data.common.gates);

        println!("circuit lde_size {:?}", data.common.lde_size());
        
        let start_time = Instant::now();
        let proof = data.prove(pw).unwrap();
        let elapsed_time = start_time.elapsed();
        println!("generate proof {:?}", elapsed_time);

        let proof_size_in_bytes = proof.to_bytes().len();
        println!("Serialized proof size: {} bytes", proof_size_in_bytes);
        let start_time = Instant::now();
        data.verify(proof.clone());
        let elapsed_time = start_time.elapsed();
        println!("verify proof {:?}", elapsed_time);
       
        Ok(())
    }


}
  // // 取 limb 的大小为2^32.

        // let limb_size = 1 << 32;

        // let k = builder.add_virtual_targets(8);
        // let e = builder.add_virtual_target();
        // let lamda = builder.add_virtual_targets(8);

        // // Compute final result k+e*lamda:

        // let mut final_result_v = lamda.clone();

        // for i in 0..final_result_v.len(){
        //     final_result_v[i] = builder.mul(final_result_v[i], e);
        // }

        // for (i, &ki) in k.iter().enumerate() {
        //     final_result_v[i] = builder.add(final_result_v[i], ki);
        // }

        //     // builder.register_public_inputs(&final_result);

        //     let k_real = generate_random_256bit_u32();
        //     let e_real = generate_random_3bit_u64();
        //     let lamda_real  = generate_random_256bit_u32();

        //     let q_original = get_predefined_prime();

        //     //compute fresult and fz

        //     //compute k*e
        //     let mut final_result_real = Vec::new();
        //     for i in 0..k_real.len(){
        //         final_result_real.push((lamda_real[i] as u64 * e_real)+k_real[i] as u64);
        //     }

        //     let base : u64 = 1<<32;
        //     let mut carries_fresult = Vec::new();
        //     let mut limbs_fresult = Vec::new();

        //     for i in 0..final_result_real.len() {
        //             // final_result[i] += carry;
        //             // carry = final_result[i] / base;
        //             // final_result[i] %= base;
        //             if i == 0{
        //                 carries_fresult.push(final_result_real[i] / base);
        //                 limbs_fresult.push(final_result_real[i] % base);
        //             } else if i>=1 && i<final_result_real.len(){
        //                 carries_fresult.push((final_result_real[i]+carries_fresult[i-1] )/ base);
        //                 limbs_fresult.push((final_result_real[i]+carries_fresult[i-1]) % base);
        //             }

        //     }

        //     while carries_fresult[carries_fresult.len()-1]>0{
        //         limbs_fresult.push(carries_fresult[carries_fresult.len()-1]%base);
        //         carries_fresult.push(carries_fresult[carries_fresult.len()-1]/base);
        //     }

        //     // Convert final_result to an Integer
        //     let mut final_result_int = BigUint::zero();
        //         for (i, &limb) in final_result_real.iter().enumerate() {
        //             final_result_int += BigUint::from(limb) << (32 * i);
        //     }

        //     // Compute p and r
        //     let p = final_result_int.clone() / q_original.clone();
        //     let r = final_result_int.clone() % q_original.clone();
        //     assert!(p.clone()*q_original.clone()+r.clone() == final_result_int);
        //     // Convert p and r back to 2^32 base
        //     let mut p_limbs = Vec::new();
        //     let mut r_limbs = Vec::new();
        //     let mut q_limbs = Vec::new();

        //     let mut temp_p = p.clone();
        //     let mut temp_r = r.clone();
        //     let mut temp_q = q_original.clone();

        //     while temp_p > BigUint::zero() {
        //         p_limbs.push((&temp_p % BigUint::from(base)).to_u64().unwrap());
        //         temp_p = temp_p / BigUint::from(base);
        //     }

        //     while temp_r > BigUint::zero() {
        //         r_limbs.push((&temp_r % BigUint::from(base )).to_u64().unwrap());
        //         temp_r = temp_r / BigUint::from(base);
        //     }

        //     while temp_q > BigUint::zero() {
        //         q_limbs.push((&temp_q % BigUint::from(base )).to_u64().unwrap());
        //         temp_q = temp_q / BigUint::from(base);
        //     }
        //     println!("p_limbs length{:}",p_limbs.len());

        //     // Compute p_limbs * q_limbs + r_limbs
        //     let max_len_pqr = p_limbs.len() + q_limbs.len() - 1;

        //     let mut max_len = 0;

        //     if p_limbs.len() != 0{

        //         max_len = std::cmp::max(max_len_pqr, r_limbs.len());

        //     }else if p_limbs.len() == 0{

        //         max_len = r_limbs.len();

        //     }

        //     let mut product_pqr = vec![0u64; max_len];
        //     for i in 0..p_limbs.len() {
        //         for j in 0..q_limbs.len() {
        //             product_pqr[i + j] += p_limbs[i] * q_limbs[j];
        //         }
        //     }
        //     for i in 0..r_limbs.len() {
        //         product_pqr[i] += r_limbs[i];
        //     }

        //     let mut carries_z = Vec::new();
        //     let mut limbs_z = Vec::new();
        //     for i in 0..product_pqr.len() {
        //         // product_pqr[i] += carry;
        //         // carry = product_pqr[i] / base;
        //         // product_pqr[i] %= base;
        //         if i == 0{
        //             carries_z.push(product_pqr[i] / base);
        //             limbs_z.push(product_pqr[i] % base);
        //         } else if i>=1 && i<product_pqr.len(){
        //             carries_z.push((product_pqr[i]+carries_z[i-1]) / base);
        //             limbs_z.push((product_pqr[i]+carries_z[i-1]) % base);
        //         }
        // }

        //     while carries_z[carries_z.len()-1]>0{
        //         limbs_z.push(carries_z[carries_z.len()-1]%base);
        //         carries_z.push(carries_z[carries_z.len()-1]/base);
        //     }

        //     println!("carries_fresult:{}",carries_fresult.len());
        //     println!("limbs_fresult:{}",limbs_fresult.len());
        //     println!("carries_z:{}",carries_z.len());
        //     println!("limbs_z:{}",limbs_z.len());
        //     println!("p_limbs:{}",p_limbs.len());
        //     println!("q_limbs:{}",q_limbs.len());
        //     println!("r_limbs:{}",r_limbs.len());

        //     if limbs_fresult == limbs_z {
        //         println!("limbs_fresult and limbs_z are identical.");
        //     } else {
        //         println!("limbs_fresult and limbs_z are different.");
        //     }

        //     let q_v = builder.add_virtual_targets(q_limbs.len());
        //     let carries_fresult_v = builder.add_virtual_targets(carries_fresult.len());
        //     let limbs_fresult_v = builder.add_virtual_targets(limbs_fresult.len());
        //     let carries_z_v = builder.add_virtual_targets(carries_z.len());
        //     let limbs_z_v = builder.add_virtual_targets(limbs_z.len());
        //     let p_v = builder.add_virtual_targets(p_limbs.len());
        //     let reminder_v = builder.add_virtual_targets(r_limbs.len());

        //     if limbs_fresult == limbs_z {
        //         println!("limbs_fresult_real and limbs_z_real are identical.");
        //     } else {
        //         println!("limbs_fresult_real and limbs_z_real are different.");
        //     }

        //     //wires to to final_result_modq

        //     let mut final_result_modq = Vec::new();

        //     for i in 0..carries_fresult_v.len(){

        //         if i == 0{
        //             let carryshifted = builder.mul_const(F::from_canonical_u64(limb_size), carries_fresult_v[0]);
        //             let expected_result = builder.add(carryshifted,limbs_fresult_v[0]);
        //             builder.is_equal(final_result_v[0], expected_result);
        //             final_result_modq.push(limbs_fresult_v[0]);
        //         } else if i >=1 && i<final_result_v.len(){
        //             let carryshifted = builder.mul_const(F::from_canonical_u64(limb_size), carries_fresult_v[i]);
        //             let expected_result = builder.add(carryshifted,limbs_fresult_v[i]);
        //             let new_carry = builder.add(final_result_v[i], carries_fresult_v[i-1]);
        //             builder.is_equal(new_carry, expected_result);
        //             final_result_modq.push(limbs_fresult_v[i]);
        //         } else if i >= final_result_v.len() && i<carries_fresult_v.len(){
        //             let carryshifted = builder.mul_const(F::from_canonical_u64(limb_size), carries_fresult_v[i]);
        //             let expected_result = builder.add(carryshifted,limbs_fresult_v[i]);
        //             builder.is_equal(carries_fresult_v[i-1], expected_result);
        //             final_result_modq.push(limbs_fresult_v[i]);
        //         }

        //     }

        //     let mut fz_modq = Vec::new();

        //     let max_len_pqr = p_v.len() + q_v.len() - 1;
        //     let max_len = std::cmp::max(max_len_pqr, reminder_v.len());
        //     let mut t = vec![builder.zero(); max_len];

        //     for i in 0..q_v.len(){

        //         for j in 0..p_v.len(){

        //             let term = builder.mul(q_v[i],p_v[j]);
        //             t[i+j] = builder.add(term, t[i+j]);

        //         }

        //     }

        //     for i in 0..reminder_v.len(){

        //         t[i]=builder.add(t[i], reminder_v[i]);

        //     }

        //     for i in 0..carries_z_v.len(){

        //         if i==0{
        //             let carryshifted = builder.mul_const(F::from_canonical_u64(limb_size), carries_z_v[0]);
        //             let expected_result = builder.add(carryshifted,limbs_z_v[0]);
        //             builder.is_equal(t[0], expected_result);
        //             fz_modq.push(limbs_z_v[0]);
        //         } else if i >=1 && i<t.len(){
        //             let carryshifted = builder.mul_const(F::from_canonical_u64(limb_size), carries_z_v[i]);
        //             let expected_result = builder.add(carryshifted,limbs_z_v[i]);
        //             let new_carry = builder.add(t[i], carries_z_v[i-1]);
        //             builder.is_equal(new_carry, expected_result);
        //             fz_modq.push(limbs_z_v[i]);
        //         } else if i >= t.len() && i<carries_z_v.len(){
        //             let carryshifted = builder.mul_const(F::from_canonical_u64(limb_size), carries_z_v[i]);
        //             let expected_result = builder.add(carryshifted,limbs_z_v[i]);
        //             builder.is_equal(carries_z_v[i-1], expected_result);
        //             fz_modq.push(limbs_z_v[i]);
        //         }

        //     }

        //     println!("{}", final_result_modq.len());
        //     println!("{}", fz_modq.len());
        //     assert!(final_result_modq.len() == fz_modq.len());

        //     for i in 0..final_result_modq.len(){

        //         builder.is_equal(final_result_modq[i], fz_modq[i]);

        //     }

        //     for i in 0..reminder_v.len(){
        //         builder.register_public_input(reminder_v[i]);
        //     }

        //     let limb_length = 32;

        //     // Range check for reminder

        //     for target in &reminder_v {
        //         builder.range_check(*target, limb_length);
        //     }

        //     // Range check for p

        //     for target in &p_v {
        //         builder.range_check(*target, limb_length);
        //     }

        //     // Range check for limbs_z

        //     for target in &limbs_z_v {
        //         builder.range_check(*target, limb_length);
        //     }

        //     // Range check for limbs_fresult

        //     for target in &limbs_fresult_v {
        //         builder.range_check(*target, limb_length);
        //     }

        //     // Range check ofr each element in q

        //     for target in &q_v {
        //         builder.range_check(*target, limb_length);
        //     }

        //     // Range check for each element in x
        //     for target in &lamda {
        //             builder.range_check(*target, limb_length);
        //     }

        //     // Range check for each element in c
        //     builder.range_check(e, 3);

        //     let mut pw = PartialWitness::new();

        //     assert!(reminder_v.len() == r_limbs.len());

        //     for i in 0..reminder_v.len(){
        //         pw.set_target(reminder_v[i], GoldilocksField::from_canonical_u64(r_limbs[i] as u64));
        //     }

        //     assert!(p_v.len() == p_limbs.len());

        //     for i in 0..p_v.len(){
        //         pw.set_target(p_v[i], GoldilocksField::from_canonical_u64(p_limbs[i] as u64));
        //     }

        //     assert!(carries_z_v.len() == carries_z.len());

        //     for i in 0..carries_z_v.len(){
        //         pw.set_target(carries_z_v[i], GoldilocksField::from_canonical_u64(carries_z[i] as u64));
        //     }

        //     assert!(limbs_z_v.len() == limbs_z.len());

        //     for i in 0..limbs_z_v.len(){
        //         pw.set_target(limbs_z_v[i], GoldilocksField::from_canonical_u64(limbs_z[i] as u64));
        //     }

        //     assert!(carries_fresult_v.len() == carries_fresult.len());

        //     for i in 0..carries_fresult_v.len(){
        //         pw.set_target(carries_fresult_v[i], GoldilocksField::from_canonical_u64(carries_fresult[i] as u64));
        //     }

        //     assert!(limbs_fresult_v.len() == limbs_fresult.len());

        //     for i in 0..limbs_fresult_v.len(){
        //         pw.set_target(limbs_fresult_v[i], GoldilocksField::from_canonical_u64(limbs_fresult[i] as u64));
        //     }

        //     assert!(q_v.len() == q_limbs.len());

        //     for i in 0..q_v.len(){
        //         pw.set_target(q_v[i], GoldilocksField::from_canonical_u64(q_limbs[i] as u64));
        //     }

        //     let mut count = 0;

        //     for &k_val in &k_real {
        //         pw.set_target(k[count], GoldilocksField::from_canonical_u64(k_val as u64));
        //         count = count+1;
        //     }

        //     pw.set_target(e,GoldilocksField::from_canonical_u64(e_real as u64));

        //     let mut count = 0;

        //     for &lamda_val in &lamda_real {
        //         pw.set_target(lamda[count], GoldilocksField::from_canonical_u64(lamda_val as u64));
        //         count = count+1;
        //     }
