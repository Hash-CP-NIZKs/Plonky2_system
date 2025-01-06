use std::time::Instant;
use p256::{
    ProjectivePoint as P256ProjectivePoint,
    Scalar as P256Scalar,
};
use p521::{
    ProjectivePoint as P521ProjectivePoint,
    Scalar as P521Scalar,
};
use elliptic_curve::{Field, Group}; 
use rand_core::OsRng;

fn main() {
    // in table 2, we mainly compare to pedersen-committed commit-and-prove framework,
    // the exp in the second row of table2 is different between the exp in the third row,
    // in the former case, the order of corresponding elliptic curve should be at least 768bits,
    // but in our construction, the exp refers to operations in sep256k1.
    
    // comporision of verifier time between Pinocchio+sigma and plonky2 +sigma AoK.
    // the verification of pinocchio and plonky2 can both be compute within 10ms.

    let n_values = [1, 50, 150, 200, 250, 300, 350, 400, 450, 500];

    for n in n_values.iter() {
        let p256_operations = 20 * n;
        let p521_operations = 2564 * n;

        println!("\n--- Testing with n = {} ---", n);

        // -------------------------- P-521 Test --------------------------
        
        // Generate a random point using the generator point and a random scalar
        let random_scalar_521 = P521Scalar::random(&mut OsRng);
        let p521_generator = P521ProjectivePoint::generator();
        let p521_point = p521_generator * random_scalar_521;

        // Generate a random scalar for the test
        let p521_exponent = P521Scalar::random(&mut OsRng);

        // Start timing P-521
        let p521_start = Instant::now();

        // Perform P-521 scalar multiplication
        for _ in 0..p521_operations {
            let p521_result = p521_point * p521_exponent;
            let _ = p521_result;  // Prevent compiler optimization
        }

        // Calculate P-521 elapsed time
        let p521_duration = p521_start.elapsed();
        println!("P-521: Time taken for {} scalar multiplications: {:?}", 
                 p521_operations, p521_duration);

        // -------------------------- P-256 Test --------------------------
        
        // Generate a random point using the generator point and a random scalar
        let random_scalar_256 = P256Scalar::random(&mut OsRng);
        let p256_generator = P256ProjectivePoint::generator();
        let p256_point = p256_generator * random_scalar_256;

        // Generate a random scalar for the test
        let p256_exponent = P256Scalar::random(&mut OsRng);

        // Start timing P-256
        let p256_start = Instant::now();

        // Perform P-256 scalar multiplication
        for _ in 0..p256_operations {
            let p256_result = p256_point * p256_exponent;
            let _ = p256_result;  // Prevent compiler optimization
        }

        // Calculate P-256 elapsed time
        let p256_duration = p256_start.elapsed();
        println!("P-256: Time taken for {} scalar multiplications: {:?}", 
                 p256_operations, p256_duration);

        // -------------------------- Performance Comparison --------------------------

        // Calculate the average time per operation (microseconds)
        let p521_avg = p521_duration.as_secs_f64() * 1_000_000.0 / p521_operations as f64;
        let p256_avg = p256_duration.as_secs_f64() * 1_000_000.0 / p256_operations as f64;

        println!("\nAverage time per scalar multiplication:");
        println!("P-521: {:.3} μs", p521_avg);
        println!("P-256: {:.3} μs", p256_avg);
        println!("\nP-521 to P-256 performance ratio: {:.2}x", 
                 p521_avg / p256_avg);
    }
}
