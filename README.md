# evo_prove_scratch_pad

**EVO PROVE Tier persistent workspace.** This repository is the scratch pad for
[EVO](https://github.com/machinelearning2014/artificial_mind)
(Explicit-assumption Verification Orchestrator) PROVE-tier tasks.

## Purpose

When EVO executes a PROVE-tier workflow (P1 setup -> P2 explore -> P3 build+verify
-> P4 validate -> P5 answer), this repo stores Lean 4 proof artifacts with
lake build verification.  Every theorem is a permanent, auditable proof artifact
that can be imported by future proofs.

## Structure

```
Proofs/
  <theorem>.lean          # Main proof file
lakefile.lean             # Lake project configuration
lean-toolchain            # Lean version pin
```

## How EVO Uses This Repo

### Workflow

1. **P1 Setup:** EVO declares problem_spec and proof_strategy in Prolog
2. **P2 Explore:** EVO explores patterns via python_exec
3. **P3 Build:** EVO writes .lean files to a feature branch (evo/prove-<slug>-<timestamp>)
4. **P4 Verify:** EVO runs lake build (locally or via CI workflow dispatch)
5. **P5 Answer:** EVO creates a PR with the verified theorem

### Branch convention

```
evo/prove-<theorem-slug>-<YYYYMMDD-HHMMSS>
```

Example: evo/prove-sqrt-two-irrational-20260608-143022

## lake build CI

The lake-build.yml workflow is triggered via workflow_dispatch.
It installs elan, runs lake update, downloads the mathlib cache,
and runs lake build.  Pass/fail is reported as the CI conclusion.

## Theorem Library

Over time, this repo accumulates a library of verified theorems.
Each is an importable Lean module that future proofs can depend on.
This turns one-shot verification into a growing proof asset.

## Security

- EVO writes are scoped to branches prefixed with evo/
- Main branch protection prevents direct pushes
- All proofs go through PR review with lake build verification
