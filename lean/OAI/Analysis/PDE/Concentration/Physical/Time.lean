import OAI.Analysis.PDE.Concentration.Physical.Positivity

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet
open scoped Matrix

private theorem fin_cases_one {d : ℕ} {β : Sort*} (a : β) (f : Fin (d + 1) → β) :
    Fin.cases a f (1 : Fin (d + 2)) = f 0 := by
  rw [← Fin.succ_zero_eq_one]
  rfl

theorem nullRotation_time_entry {d : ℕ} (M : OAI.Analysis.Calculus.Current.Index d → OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) :
    (matrixConjugationCLM (nullRotation d) (nullMatrixReindex d M) 0 0).re =
      OAI.Analysis.Calculus.Current.timeComponent M := by
  have hs : ((Real.sqrt 2)⁻¹) ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  let N : Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ) := nullMatrixReindex d M
  change (((OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d))ᴴ * N * OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d)) 0 0).re = _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp [
    nullRotation, Fin.sum_univ_succ, OAI.Analysis.PDE.Dirichlet.realLift_apply,
    N, nullMatrixReindex_apply, OAI.Analysis.Calculus.Current.timeComponent]
  simp only [← mul_assoc, ← pow_two, hs]
  ring

theorem physicalPacketCurrent_time_entry {d : ℕ} {ι : Type*} [Fintype ι]
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    (physicalPacketCurrent h a κ cR cI v x 0 0).re =
      OAI.Analysis.Calculus.Current.timeComponent (OAI.Analysis.Calculus.Current.sourceRegularizedCurrent h a κ cR cI v
        (physicalToNullCurrentPoint d x).1 (physicalToNullCurrentPoint d x).2) :=
  nullRotation_time_entry _

theorem physicalPacketCurrent_time_pos {d : ℕ} {ι : Type*} [Fintype ι]
    (h a : ℝ) (hh : 0 < h) (ha : a ≠ 0) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0)
    (hr : OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a (physicalToNullCurrentPoint d x).2 ≤ 0) :
    0 < (physicalPacketCurrent h a κ cR cI v x 0 0).re := by
  rw [physicalPacketCurrent_time_entry]
  exact OAI.Analysis.Calculus.Current.sourceRegularizedCurrent_time_pos h a hh ha κ cR cI v _ _ hx hr

end OAI.Analysis.PDE.Concentration
