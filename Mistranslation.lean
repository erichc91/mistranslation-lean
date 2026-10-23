import Mistranslation.Table

/-!
# The MEMS pull-in number is transcendental

A MEMS switch is a thin plate pinned at both ends above an electrode. With the gap scaled so the ends sit at 1,
the gap v obeys `v'' = μ / v²`, `v > 0` on [0, 1], `v(0) = v(1) = 1` (`MemsOde.Sol`). Push too hard and there is
no solution: the plate snaps down. The largest push that still works is about 1.4000165.

This theorem proves, starting from the equation, that the largest push exists and is transcendental.
No hypotheses: Hermite-Lindemann is proved from Yuyang Zhao's Lindemann-Weierstrass theorem (vendored, Apache 2.0).
-/

/-- **The MEMS pull-in number exists and is transcendental.** -/
theorem mems_pull_in_transcendental :
    ∃ B : ℝ, IsGreatest {μ | ∃ v v' : ℝ → ℝ, MemsOde.Sol μ v v'} B ∧ Transcendental ℚ B :=
  MemsOde.mems_break_end_to_end LindemannBridge.hermite_lindemann

#print axioms mems_pull_in_transcendental
