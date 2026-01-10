//! Corpus-based conformance tests.
//!
//! These tests run all vectors from the Lean-generated corpus.json
//! and verify the Rust implementation produces matching results.
//!
//! # Requirements
//!
//! - CONF-001: Load corpus.json
//! - CONF-002: Run all test vectors
//! - CONF-003: Report failures with details

use jolt_oracle::conformance::{CorpusRunner, TestResult};
use std::path::Path;

/// Path to the corpus file relative to the project root.
const CORPUS_PATH: &str = "../jolt_oracle/corpus/corpus.json";

/// Load and run the full corpus.
#[test]
fn test_full_corpus() {
    let corpus_path = Path::new(env!("CARGO_MANIFEST_DIR")).join(CORPUS_PATH);

    if !corpus_path.exists() {
        eprintln!(
            "Corpus file not found at {:?}, skipping corpus tests",
            corpus_path
        );
        return;
    }

    let runner = CorpusRunner::load(&corpus_path).expect("Failed to load corpus");

    println!("Loaded corpus with {} vectors", runner.vector_count());
    println!("Manifest: {:?}", runner.manifest());

    let results = runner.run_all();

    // Print summary
    println!("\n=== Corpus Conformance Results ===");
    println!("{}", results.summary());

    // Print failures
    if !results.failures().is_empty() {
        println!("\nFailures:");
        for (id, result) in results.failures() {
            if let TestResult::Fail { expected, actual } = result {
                println!("  {} - expected: {}, actual: {}", id, expected, actual);
            }
        }
    }

    // Print errors
    if !results.error_details().is_empty() {
        println!("\nErrors:");
        for (id, result) in results.error_details() {
            if let TestResult::Error { message } = result {
                println!("  {} - {}", id, message);
            }
        }
    }

    // Assert all tests passed (excluding skips)
    assert!(
        results.all_passed(),
        "Corpus conformance failed: {}",
        results.summary()
    );
}

/// Test that we can load the corpus manifest.
#[test]
fn test_corpus_manifest() {
    let corpus_path = Path::new(env!("CARGO_MANIFEST_DIR")).join(CORPUS_PATH);

    if !corpus_path.exists() {
        eprintln!("Corpus file not found, skipping");
        return;
    }

    let runner = CorpusRunner::load(&corpus_path).expect("Failed to load corpus");
    let manifest = runner.manifest();

    assert_eq!(manifest.format_version, "corpus-v1");
    assert_eq!(manifest.version, "1");

    // Verify BLS12-381 modulus
    assert_eq!(
        manifest.modulus_decimal,
        "52435875175126190479447740508185965837690552500527637822603658699938581184513"
    );
}

/// Test Fr canonical vectors.
#[test]
fn test_corpus_fr_canonical() {
    let corpus_path = Path::new(env!("CARGO_MANIFEST_DIR")).join(CORPUS_PATH);

    if !corpus_path.exists() {
        eprintln!("Corpus file not found, skipping");
        return;
    }

    let runner = CorpusRunner::load(&corpus_path).expect("Failed to load corpus");
    let results = runner.run_all();

    // Count fr_canonical tests
    let fr_tests: Vec<_> = results
        .details
        .iter()
        .filter(|(id, _)| id.starts_with("fr_"))
        .collect();

    println!("Fr tests: {} total", fr_tests.len());

    let passed: Vec<_> = fr_tests
        .iter()
        .filter(|(_, r)| r.is_pass())
        .collect();

    println!("Fr tests passed: {}", passed.len());

    // All Fr tests should pass
    for (id, result) in &fr_tests {
        if let TestResult::Fail { expected, actual } = result {
            panic!("{} failed: expected={}, actual={}", id, expected, actual);
        }
    }
}

/// Test Poseidon vectors.
#[test]
fn test_corpus_poseidon() {
    let corpus_path = Path::new(env!("CARGO_MANIFEST_DIR")).join(CORPUS_PATH);

    if !corpus_path.exists() {
        eprintln!("Corpus file not found, skipping");
        return;
    }

    let runner = CorpusRunner::load(&corpus_path).expect("Failed to load corpus");
    let results = runner.run_all();

    // Count poseidon tests
    let poseidon_tests: Vec<_> = results
        .details
        .iter()
        .filter(|(id, _)| id.starts_with("poseidon_"))
        .collect();

    println!("Poseidon tests: {} total", poseidon_tests.len());

    let passed: Vec<_> = poseidon_tests
        .iter()
        .filter(|(_, r)| r.is_pass())
        .collect();

    println!("Poseidon tests passed: {}", passed.len());

    // All Poseidon tests should pass
    for (id, result) in &poseidon_tests {
        if let TestResult::Fail { expected, actual } = result {
            panic!("{} failed: expected={}, actual={}", id, expected, actual);
        }
    }
}

/// Test negative (error) vectors.
#[test]
fn test_corpus_negative_cases() {
    let corpus_path = Path::new(env!("CARGO_MANIFEST_DIR")).join(CORPUS_PATH);

    if !corpus_path.exists() {
        eprintln!("Corpus file not found, skipping");
        return;
    }

    let runner = CorpusRunner::load(&corpus_path).expect("Failed to load corpus");
    let results = runner.run_all();

    // Count negative tests
    let negative_tests: Vec<_> = results
        .details
        .iter()
        .filter(|(id, _)| id.starts_with("negative_"))
        .collect();

    println!("Negative tests: {} total", negative_tests.len());

    let passed: Vec<_> = negative_tests
        .iter()
        .filter(|(_, r)| r.is_pass())
        .collect();

    println!("Negative tests passed: {}", passed.len());

    // All negative tests should pass
    for (id, result) in &negative_tests {
        if let TestResult::Fail { expected, actual } = result {
            panic!("{} failed: expected={}, actual={}", id, expected, actual);
        }
    }
}
