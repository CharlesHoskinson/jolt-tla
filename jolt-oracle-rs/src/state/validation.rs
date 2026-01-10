//! VMStateV1 validation functions.

use super::types::VMStateV1;
use crate::error::{ErrorCode, OracleResult};

/// Validate that regs[0] is zero (RISC-V x0 invariant).
fn validate_register_x0(state: &VMStateV1) -> OracleResult<()> {
    if state.regs[0] != 0 {
        return Err(ErrorCode::E407_RegisterX0NonZero(state.regs[0].to_string()));
    }
    Ok(())
}

/// Validate halted flag is 0 or 1 per specification section 11.5.
fn validate_halted(state: &VMStateV1) -> OracleResult<()> {
    if state.halted != 0 && state.halted != 1 {
        return Err(ErrorCode::E404_InvalidHalted);
    }
    Ok(())
}

/// Validate termination invariants per specification section 11.5.1.
///
/// - halted = 0 -> exit_code = 0
/// - halted = 1 -> exit_code <= 255
fn validate_termination(state: &VMStateV1) -> OracleResult<()> {
    if state.halted == 0 {
        if state.exit_code != 0 {
            return Err(ErrorCode::E405_TerminationInvariant(
                "running state must have exit_code=0".to_string(),
            ));
        }
    } else {
        // halted == 1
        if state.exit_code > 255 {
            return Err(ErrorCode::E402_OutOfRange(
                "exit_code must be <= 255".to_string(),
            ));
        }
    }
    Ok(())
}

/// Validate config_tags are sorted by name bytes (lexicographic).
fn validate_config_tags_order(state: &VMStateV1) -> OracleResult<()> {
    for window in state.config_tags.windows(2) {
        if window[0].name >= window[1].name {
            return Err(ErrorCode::E401_OrderingViolation(
                "config_tags must be sorted by name bytes".to_string(),
            ));
        }
    }
    Ok(())
}

/// Full validation of VM state.
pub fn validate_vm_state(state: &VMStateV1) -> OracleResult<()> {
    validate_register_x0(state)?;
    validate_halted(state)?;
    validate_termination(state)?;
    validate_config_tags_order(state)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::types::ConfigTag;

    #[test]
    fn test_valid_state() {
        let state = VMStateV1::default();
        assert!(validate_vm_state(&state).is_ok());
    }

    #[test]
    fn test_invalid_x0() {
        let mut state = VMStateV1::default();
        state.regs[0] = 42;
        assert!(matches!(
            validate_vm_state(&state),
            Err(ErrorCode::E407_RegisterX0NonZero(_))
        ));
    }

    #[test]
    fn test_invalid_halted() {
        let mut state = VMStateV1::default();
        state.halted = 5;
        assert!(matches!(
            validate_vm_state(&state),
            Err(ErrorCode::E404_InvalidHalted)
        ));
    }

    #[test]
    fn test_termination_running_with_exit_code() {
        let mut state = VMStateV1::default();
        state.halted = 0;
        state.exit_code = 1;
        assert!(matches!(
            validate_vm_state(&state),
            Err(ErrorCode::E405_TerminationInvariant(_))
        ));
    }

    #[test]
    fn test_termination_halted_exit_code_too_large() {
        let mut state = VMStateV1::default();
        state.halted = 1;
        state.exit_code = 256;
        assert!(matches!(
            validate_vm_state(&state),
            Err(ErrorCode::E402_OutOfRange(_))
        ));
    }

    #[test]
    fn test_config_tags_unsorted() {
        let mut state = VMStateV1::default();
        state.config_tags = vec![
            ConfigTag::new(b"zzz".to_vec(), vec![]),
            ConfigTag::new(b"aaa".to_vec(), vec![]),
        ];
        assert!(matches!(
            validate_vm_state(&state),
            Err(ErrorCode::E401_OrderingViolation(_))
        ));
    }

    #[test]
    fn test_config_tags_sorted() {
        let mut state = VMStateV1::default();
        state.config_tags = vec![
            ConfigTag::new(b"aaa".to_vec(), vec![]),
            ConfigTag::new(b"bbb".to_vec(), vec![]),
            ConfigTag::new(b"zzz".to_vec(), vec![]),
        ];
        assert!(validate_vm_state(&state).is_ok());
    }
}
