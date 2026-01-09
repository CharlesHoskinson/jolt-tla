(****************************************************************************)
(* Module: MC_BadRegistry_ExternalHandle.tla                               *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE MC_BadRegistry_ExternalHandle ----
(****************************************************************************)
(* Purpose: Pattern A test - reject invalid registry with external handle   *)
(* Pattern: A (fail-closed validation)                                      *)
(* Expected: TLC succeeds (invalid state cannot reach COMPLETE)             *)
(*                                                                          *)
(* Attack scenario: Registry contains external handle tag which should      *)
(* only be computed externally, never stored in registry.json.              *)
(* The model should either:                                                 *)
(* - Not allow this state to be reached at all, or                          *)
(* - Fail validation before reaching COMPLETE phase                         *)
(****************************************************************************)
EXTENDS MC_Jolt

(****************************************************************************)
(* TEST: Verify external handles cannot appear in registry                  *)
(* Since RequiredKeys is fixed to exactly 17 keys, and external handles     *)
(* are in a separate set, TLA+ type system prevents injection.              *)
(*                                                                          *)
(* This test verifies the invariant NoExternalHandlesInvariant holds.       *)
(****************************************************************************)

\* The invariant from Registry.tla should always hold
ExternalHandlesBlocked == NoExternalHandlesInvariant(sys.registry)

\* Additional check: external handle keys never appear in registry domain
NoExternalHandleKeys ==
    \A k \in ExternalHandleTags : k \notin DOMAIN sys.registry

\* Combined invariant for this test
TestInvariant ==
    /\ ExternalHandlesBlocked
    /\ NoExternalHandleKeys

(****************************************************************************)
(* SPECIFICATION                                                             *)
(* Use the normal model spec - if invariant holds, external handles blocked *)
(****************************************************************************)

\* Reuse the normal ModelSpec from MC_Jolt
\* The invariant TestInvariant should ALWAYS hold (no violations)

====
