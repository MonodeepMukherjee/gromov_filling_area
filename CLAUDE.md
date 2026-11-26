# Neuro-Symbolic Prover Protocol (Gromov's Filling Area Conjecture)

## Mandatory Compiler-in-the-Loop Rule
After EVERY edit to any `.lean` file, you MUST run:
`python3 scripts/verify_and_log.py <ModuleName> <FilePath> claude-app`
(For example: `python3 scripts/verify_and_log.py GromovFillingArea.Kuratowski GromovFillingArea/Kuratowski.lean claude-app`)

Do NOT stop until the script prints `[PASS]` with zero errors and zero `sorry` warnings.

## Strict Formalization Rules
1. Keep the `module` keyword at the top and wrap declarations in `@[expose] public section`.
2. NEVER introduce `axiom` or `admit`.
3. Keep every line under 100 characters to pass Mathlib style linters.
4. Decompose hard differential/metric geometry steps into small, reusable helper lemmas.
