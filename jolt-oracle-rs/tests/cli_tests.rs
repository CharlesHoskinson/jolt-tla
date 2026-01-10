//! CLI integration tests.
//!
//! Tests the oracle CLI commands by invoking the binary as a subprocess.

use std::io::Write;
use std::process::{Command, Stdio};

fn oracle_path() -> std::path::PathBuf {
    // Find the oracle binary in the target directory
    let mut path = std::env::current_exe()
        .ok()
        .and_then(|p| p.parent().map(|p| p.to_path_buf()))
        .unwrap_or_default();

    // Navigate to the deps directory's sibling (the main binary location)
    if path.ends_with("deps") {
        path.pop();
    }

    if cfg!(windows) {
        path.join("oracle.exe")
    } else {
        path.join("oracle")
    }
}

fn run_command(cmd: &str, input: &str) -> (i32, String, String) {
    let oracle = oracle_path();
    let mut child = Command::new(&oracle)
        .arg(cmd)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|e| panic!("Failed to spawn oracle at {:?}: {}", oracle, e));

    {
        let stdin = child.stdin.as_mut().unwrap();
        stdin.write_all(input.as_bytes()).unwrap();
    }

    let output = child.wait_with_output().unwrap();
    let code = output.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    (code, stdout, stderr)
}

fn run_digest(input: &str) -> (i32, String, String) {
    run_command("digest", input)
}

fn run_verify(input: &str) -> (i32, String, String) {
    run_command("verify", input)
}

// ============================================================================
// Digest Command Tests
// ============================================================================

#[test]
fn cli_digest_minimal_state() {
    let input = r#"{
        "program_hash": "0000000000000000000000000000000000000000000000000000000000000000",
        "state": {
            "pc": 0,
            "regs": [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
            "step_counter": 0,
            "rw_mem_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "io_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "halted": 0,
            "exit_code": 0,
            "config_tags": []
        }
    }"#;

    let (code, stdout, _stderr) = run_digest(input);
    assert_eq!(code, 0, "Expected success exit code");
    assert!(
        stdout.contains("\"ok\""),
        "Expected ok in output: {}",
        stdout
    );
    assert!(
        stdout.contains(
            "24421670062301725635551677633693836338234896090794496795972501815695727753187"
        ),
        "Expected correct digest: {}",
        stdout
    );
}

#[test]
fn cli_digest_halted_state() {
    let input = r#"{
        "program_hash": "deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef",
        "state": {
            "pc": 8192,
            "regs": [0,100,200,300,400,500,600,700,800,900,1000,1100,1200,1300,1400,1500,1600,1700,1800,1900,2000,2100,2200,2300,2400,2500,2600,2700,2800,2900,3000,3100],
            "step_counter": 50000,
            "rw_mem_root": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            "io_root": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
            "halted": 1,
            "exit_code": 42,
            "config_tags": []
        }
    }"#;

    let (code, stdout, _stderr) = run_digest(input);
    assert_eq!(code, 0, "Expected success exit code");
    assert!(
        stdout.contains("\"ok\""),
        "Expected ok in output: {}",
        stdout
    );
    assert!(
        stdout.contains(
            "40400183813884747956300889570234739091911790924111649960538043847858548402419"
        ),
        "Expected correct digest: {}",
        stdout
    );
}

#[test]
fn cli_digest_invalid_x0() {
    let input = r#"{
        "program_hash": "0000000000000000000000000000000000000000000000000000000000000000",
        "state": {
            "pc": 0,
            "regs": [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
            "step_counter": 0,
            "rw_mem_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "io_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "halted": 0,
            "exit_code": 0,
            "config_tags": []
        }
    }"#;

    let (code, stdout, _stderr) = run_digest(input);
    assert_eq!(code, 1, "Expected failure exit code");
    assert!(
        stdout.contains("\"err\""),
        "Expected err in output: {}",
        stdout
    );
    assert!(
        stdout.contains("407"),
        "Expected E407 error code: {}",
        stdout
    );
    assert!(
        stdout.contains("E407_RegisterX0NonZero"),
        "Expected error name: {}",
        stdout
    );
}

#[test]
fn cli_digest_invalid_halted() {
    let input = r#"{
        "program_hash": "0000000000000000000000000000000000000000000000000000000000000000",
        "state": {
            "pc": 0,
            "regs": [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
            "step_counter": 0,
            "rw_mem_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "io_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "halted": 2,
            "exit_code": 0,
            "config_tags": []
        }
    }"#;

    let (code, stdout, _stderr) = run_digest(input);
    assert_eq!(code, 1, "Expected failure exit code");
    assert!(
        stdout.contains("\"err\""),
        "Expected err in output: {}",
        stdout
    );
    assert!(
        stdout.contains("404"),
        "Expected E404 error code: {}",
        stdout
    );
}

#[test]
fn cli_digest_invalid_json() {
    let input = "not valid json";

    let (code, stdout, _stderr) = run_digest(input);
    assert_eq!(code, 1, "Expected failure exit code");
    assert!(
        stdout.contains("\"err\""),
        "Expected err in output: {}",
        stdout
    );
    assert!(
        stdout.contains("100"),
        "Expected E100 error code: {}",
        stdout
    );
}

#[test]
fn cli_digest_typical_state() {
    let input = r#"{
        "program_hash": "abcd1234567890abcd1234567890abcd1234567890abcd1234567890abcd1234",
        "state": {
            "pc": 4096,
            "regs": [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],
            "step_counter": 1000,
            "rw_mem_root": "1111111111111111111111111111111111111111111111111111111111111111",
            "io_root": "2222222222222222222222222222222222222222222222222222222222222222",
            "halted": 0,
            "exit_code": 0,
            "config_tags": []
        }
    }"#;

    let (code, stdout, _stderr) = run_digest(input);
    assert_eq!(code, 0, "Expected success exit code");
    assert!(
        stdout.contains("\"ok\""),
        "Expected ok in output: {}",
        stdout
    );
    assert!(
        stdout.contains(
            "30919686901236335602438576816898388225550310633849398790605613577781839025832"
        ),
        "Expected correct digest: {}",
        stdout
    );
}

#[test]
fn cli_digest_state_with_empty_config_tags() {
    let input = r#"{
        "program_hash": "cafebabecafebabecafebabecafebabecafebabecafebabecafebabecafebabe",
        "state": {
            "pc": 4096,
            "regs": [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
            "step_counter": 100,
            "rw_mem_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "io_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "halted": 0,
            "exit_code": 0,
            "config_tags": []
        }
    }"#;

    let (code, stdout, _stderr) = run_digest(input);
    assert_eq!(code, 0, "Expected success exit code");
    assert!(
        stdout.contains("\"ok\""),
        "Expected ok in output: {}",
        stdout
    );
    assert!(
        stdout.contains(
            "51269420250097274214666708236162143841421999722140888943312460699788950625363"
        ),
        "Expected correct digest: {}",
        stdout
    );
}

// ============================================================================
// Verify Command Tests
// ============================================================================

#[test]
fn cli_verify_correct_digest() {
    let input = r#"{
        "program_hash": "0000000000000000000000000000000000000000000000000000000000000000",
        "state": {
            "pc": 0,
            "regs": [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
            "step_counter": 0,
            "rw_mem_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "io_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "halted": 0,
            "exit_code": 0,
            "config_tags": []
        },
        "expected_digest": "24421670062301725635551677633693836338234896090794496795972501815695727753187"
    }"#;

    let (code, stdout, _stderr) = run_verify(input);
    assert_eq!(code, 0, "Expected success exit code for valid digest");
    assert!(
        stdout.contains("\"ok\""),
        "Expected ok in output: {}",
        stdout
    );
    assert!(
        stdout.contains("\"valid\":true"),
        "Expected valid:true: {}",
        stdout
    );
}

#[test]
fn cli_verify_incorrect_digest() {
    let input = r#"{
        "program_hash": "0000000000000000000000000000000000000000000000000000000000000000",
        "state": {
            "pc": 0,
            "regs": [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
            "step_counter": 0,
            "rw_mem_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "io_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "halted": 0,
            "exit_code": 0,
            "config_tags": []
        },
        "expected_digest": "12345"
    }"#;

    let (code, stdout, _stderr) = run_verify(input);
    assert_eq!(code, 1, "Expected failure exit code for invalid digest");
    assert!(
        stdout.contains("\"ok\""),
        "Expected ok in output: {}",
        stdout
    );
    assert!(
        stdout.contains("\"valid\":false"),
        "Expected valid:false: {}",
        stdout
    );
    assert!(
        stdout.contains(
            "24421670062301725635551677633693836338234896090794496795972501815695727753187"
        ),
        "Expected computed_digest in output: {}",
        stdout
    );
    assert!(
        stdout.contains("12345"),
        "Expected expected_digest in output: {}",
        stdout
    );
}

#[test]
fn cli_verify_halted_state_correct() {
    let input = r#"{
        "program_hash": "deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef",
        "state": {
            "pc": 8192,
            "regs": [0,100,200,300,400,500,600,700,800,900,1000,1100,1200,1300,1400,1500,1600,1700,1800,1900,2000,2100,2200,2300,2400,2500,2600,2700,2800,2900,3000,3100],
            "step_counter": 50000,
            "rw_mem_root": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            "io_root": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
            "halted": 1,
            "exit_code": 42,
            "config_tags": []
        },
        "expected_digest": "40400183813884747956300889570234739091911790924111649960538043847858548402419"
    }"#;

    let (code, stdout, _stderr) = run_verify(input);
    assert_eq!(code, 0, "Expected success exit code");
    assert!(
        stdout.contains("\"valid\":true"),
        "Expected valid:true: {}",
        stdout
    );
}

#[test]
fn cli_verify_invalid_state_error() {
    let input = r#"{
        "program_hash": "0000000000000000000000000000000000000000000000000000000000000000",
        "state": {
            "pc": 0,
            "regs": [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
            "step_counter": 0,
            "rw_mem_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "io_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "halted": 0,
            "exit_code": 0,
            "config_tags": []
        },
        "expected_digest": "12345"
    }"#;

    let (code, stdout, _stderr) = run_verify(input);
    assert_eq!(code, 1, "Expected failure exit code for invalid state");
    assert!(
        stdout.contains("\"err\""),
        "Expected err in output: {}",
        stdout
    );
    assert!(
        stdout.contains("407"),
        "Expected E407 error code: {}",
        stdout
    );
}

#[test]
fn cli_verify_invalid_json() {
    let input = "not valid json";

    let (code, stdout, _stderr) = run_verify(input);
    assert_eq!(code, 1, "Expected failure exit code");
    assert!(
        stdout.contains("\"err\""),
        "Expected err in output: {}",
        stdout
    );
    assert!(
        stdout.contains("100"),
        "Expected E100 error code: {}",
        stdout
    );
}

#[test]
fn cli_verify_typical_state_correct() {
    let input = r#"{
        "program_hash": "abcd1234567890abcd1234567890abcd1234567890abcd1234567890abcd1234",
        "state": {
            "pc": 4096,
            "regs": [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],
            "step_counter": 1000,
            "rw_mem_root": "1111111111111111111111111111111111111111111111111111111111111111",
            "io_root": "2222222222222222222222222222222222222222222222222222222222222222",
            "halted": 0,
            "exit_code": 0,
            "config_tags": []
        },
        "expected_digest": "30919686901236335602438576816898388225550310633849398790605613577781839025832"
    }"#;

    let (code, stdout, _stderr) = run_verify(input);
    assert_eq!(code, 0, "Expected success exit code");
    assert!(
        stdout.contains("\"valid\":true"),
        "Expected valid:true: {}",
        stdout
    );
}

#[test]
fn cli_verify_zero_digest() {
    // Test with expected_digest = "0"
    let input = r#"{
        "program_hash": "0000000000000000000000000000000000000000000000000000000000000000",
        "state": {
            "pc": 0,
            "regs": [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
            "step_counter": 0,
            "rw_mem_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "io_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "halted": 0,
            "exit_code": 0,
            "config_tags": []
        },
        "expected_digest": "0"
    }"#;

    let (code, stdout, _stderr) = run_verify(input);
    // The actual digest is not 0, so this should fail
    assert_eq!(code, 1, "Expected failure exit code");
    assert!(
        stdout.contains("\"valid\":false"),
        "Expected valid:false: {}",
        stdout
    );
}

// ============================================================================
// Generate Command Tests
// ============================================================================

use std::fs;
use std::path::PathBuf;

fn run_generate(vector_type: &str, input_path: &str) -> (i32, String, String) {
    let oracle = oracle_path();
    let output = Command::new(&oracle)
        .args(["generate", vector_type, input_path])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap_or_else(|e| panic!("Failed to run oracle: {}", e));

    let code = output.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    (code, stdout, stderr)
}

fn run_generate_with_output(
    vector_type: &str,
    input_path: &str,
    output_path: &str,
) -> (i32, String, String) {
    let oracle = oracle_path();
    let output = Command::new(&oracle)
        .args(["generate", vector_type, input_path, "-o", output_path])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap_or_else(|e| panic!("Failed to run oracle: {}", e));

    let code = output.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    (code, stdout, stderr)
}

fn temp_file_path(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!("jolt_oracle_test_{}", name))
}

#[test]
fn cli_generate_state_digest() {
    // Create a temp input file
    let input_path = temp_file_path("gen_minimal.json");
    let input_content = r#"{
        "program_hash": "0000000000000000000000000000000000000000000000000000000000000000",
        "state": {
            "pc": 0,
            "regs": [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
            "step_counter": 0,
            "rw_mem_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "io_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "halted": 0,
            "exit_code": 0,
            "config_tags": []
        }
    }"#;
    fs::write(&input_path, input_content).unwrap();

    let (code, stdout, _stderr) = run_generate("state_digest", input_path.to_str().unwrap());

    // Clean up
    let _ = fs::remove_file(&input_path);

    assert_eq!(code, 0, "Expected success exit code");
    assert!(
        stdout.contains("\"vectors\""),
        "Expected vectors in output: {}",
        stdout
    );
    assert!(
        stdout.contains("\"type\":\"state_digest\""),
        "Expected type field: {}",
        stdout
    );
    assert!(
        stdout.contains("\"name\":\"jolt_oracle_test_gen_minimal\""),
        "Expected name from filename: {}",
        stdout
    );
    assert!(
        stdout.contains(
            "24421670062301725635551677633693836338234896090794496795972501815695727753187"
        ),
        "Expected correct digest in expected field: {}",
        stdout
    );
}

#[test]
fn cli_generate_halted_state() {
    let input_path = temp_file_path("gen_halted.json");
    let input_content = r#"{
        "program_hash": "deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef",
        "state": {
            "pc": 8192,
            "regs": [0,100,200,300,400,500,600,700,800,900,1000,1100,1200,1300,1400,1500,1600,1700,1800,1900,2000,2100,2200,2300,2400,2500,2600,2700,2800,2900,3000,3100],
            "step_counter": 50000,
            "rw_mem_root": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            "io_root": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
            "halted": 1,
            "exit_code": 42,
            "config_tags": []
        }
    }"#;
    fs::write(&input_path, input_content).unwrap();

    let (code, stdout, _stderr) = run_generate("state_digest", input_path.to_str().unwrap());

    let _ = fs::remove_file(&input_path);

    assert_eq!(code, 0, "Expected success exit code");
    assert!(
        stdout.contains("\"vectors\""),
        "Expected vectors in output: {}",
        stdout
    );
    assert!(
        stdout.contains(
            "40400183813884747956300889570234739091911790924111649960538043847858548402419"
        ),
        "Expected correct digest: {}",
        stdout
    );
}

#[test]
fn cli_generate_with_output_file() {
    let input_path = temp_file_path("gen_out_input.json");
    let output_path = temp_file_path("gen_out_output.json");
    let input_content = r#"{
        "program_hash": "0000000000000000000000000000000000000000000000000000000000000000",
        "state": {
            "pc": 0,
            "regs": [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
            "step_counter": 0,
            "rw_mem_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "io_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "halted": 0,
            "exit_code": 0,
            "config_tags": []
        }
    }"#;
    fs::write(&input_path, input_content).unwrap();

    let (code, stdout, _stderr) = run_generate_with_output(
        "state_digest",
        input_path.to_str().unwrap(),
        output_path.to_str().unwrap(),
    );

    assert_eq!(code, 0, "Expected success exit code");
    assert!(
        stdout.contains("Generated test vector written to:"),
        "Expected confirmation: {}",
        stdout
    );

    // Read and verify output file
    let output_content = fs::read_to_string(&output_path).unwrap();
    assert!(
        output_content.contains("\"vectors\""),
        "Output file should have vectors: {}",
        output_content
    );
    assert!(
        output_content.contains(
            "24421670062301725635551677633693836338234896090794496795972501815695727753187"
        ),
        "Output file should have correct digest: {}",
        output_content
    );

    // Clean up
    let _ = fs::remove_file(&input_path);
    let _ = fs::remove_file(&output_path);
}

#[test]
fn cli_generate_invalid_type() {
    let input_path = temp_file_path("gen_invalid_type.json");
    let input_content = r#"{
        "program_hash": "0000000000000000000000000000000000000000000000000000000000000000",
        "state": {
            "pc": 0,
            "regs": [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
            "step_counter": 0,
            "rw_mem_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "io_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "halted": 0,
            "exit_code": 0,
            "config_tags": []
        }
    }"#;
    fs::write(&input_path, input_content).unwrap();

    let (code, stdout, _stderr) = run_generate("unknown_type", input_path.to_str().unwrap());

    let _ = fs::remove_file(&input_path);

    assert_eq!(code, 1, "Expected failure exit code");
    assert!(
        stdout.contains("\"status\":\"ERROR\""),
        "Expected error status: {}",
        stdout
    );
    assert!(
        stdout.contains("E106_UnexpectedType"),
        "Expected type error: {}",
        stdout
    );
}

#[test]
fn cli_generate_file_not_found() {
    let (code, stdout, _stderr) = run_generate("state_digest", "/nonexistent/path/file.json");

    assert_eq!(code, 1, "Expected failure exit code");
    assert!(
        stdout.contains("\"status\":\"ERROR\""),
        "Expected error status: {}",
        stdout
    );
    assert!(
        stdout.contains("E900_FileNotFound"),
        "Expected file not found error: {}",
        stdout
    );
}

#[test]
fn cli_generate_invalid_json() {
    let input_path = temp_file_path("gen_bad_json.json");
    fs::write(&input_path, "not valid json").unwrap();

    let (code, stdout, _stderr) = run_generate("state_digest", input_path.to_str().unwrap());

    let _ = fs::remove_file(&input_path);

    assert_eq!(code, 1, "Expected failure exit code");
    assert!(
        stdout.contains("\"status\":\"ERROR\""),
        "Expected error status: {}",
        stdout
    );
    assert!(
        stdout.contains("E100_InvalidJSON"),
        "Expected JSON error: {}",
        stdout
    );
}

#[test]
fn cli_generate_invalid_state() {
    let input_path = temp_file_path("gen_bad_state.json");
    let input_content = r#"{
        "program_hash": "0000000000000000000000000000000000000000000000000000000000000000",
        "state": {
            "pc": 0,
            "regs": [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
            "step_counter": 0,
            "rw_mem_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "io_root": "0000000000000000000000000000000000000000000000000000000000000000",
            "halted": 0,
            "exit_code": 0,
            "config_tags": []
        }
    }"#;
    fs::write(&input_path, input_content).unwrap();

    let (code, stdout, _stderr) = run_generate("state_digest", input_path.to_str().unwrap());

    let _ = fs::remove_file(&input_path);

    assert_eq!(code, 1, "Expected failure exit code");
    assert!(
        stdout.contains("\"status\":\"ERROR\""),
        "Expected error status: {}",
        stdout
    );
    assert!(
        stdout.contains("E407_RegisterX0NonZero"),
        "Expected x0 error: {}",
        stdout
    );
}
