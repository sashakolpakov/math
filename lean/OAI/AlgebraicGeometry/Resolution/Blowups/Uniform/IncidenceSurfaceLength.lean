import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceSurfaceProgram

/-! # Incidence Surface Length -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform

noncomputable section

/-! The number of actual steps depends only on the prescribed levels and the initial number of boundary labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem IncidenceSurfaceLength.Construction.card_iteratedBoundaryLabels (N : ℕ) (β : Type) [Fintype β] :
    Fintype.card (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β) = Fintype.card β + N := by
  induction N generalizing β with
  | zero => exact (Nat.add_zero _).symm
  | succ N ih =>
      change Fintype.card (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N (Option β)) = Fintype.card β + (N + 1)
      rw [ih, Fintype.card_option]
      omega

def IncidenceSurfaceLength.Construction.surfaceIncidenceProgramStepCount (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, k => if (n + 1).factorial ≤ m + 1 then
      2 ^ k + surfaceIncidenceProgramStepCount n m (k + 2 ^ k) else 0

theorem IncidenceSurfaceLength.Construction.surfaceIncidenceProgramStepCount_of_lt (n m k : ℕ) (h : m < (n + 1).factorial) :
    IncidenceSurfaceLength.Construction.surfaceIncidenceProgramStepCount n m k = 0 := by
  cases m with
  | zero => rfl
  | succ m => exact ite_eq_right (Nat.not_le.mpr h)

theorem IncidenceSurfaceProgram.Construction.UniformIncidenceSurfaceProgram.stepCount
    {n m : ℕ} {β : Type} [Fintype β] {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : IncidenceSurfaceProgram.Construction.UniformIncidenceSurfaceProgram n m β X f J D Y g K P) :
    P.stepCount = IncidenceSurfaceLength.Construction.surfaceIncidenceProgramStepCount n m (Fintype.card β) := by
  classical
  induction T with
  | terminal hstop A ht =>
      exact (IncidenceSurfaceLength.Construction.surfaceIncidenceProgramStepCount_of_lt _ _ _ hstop).symm
  | refine A hb hd hlevel AM P hcenters hcount hP Q tail ih =>
      rw [Smooth.ControlPrefix.Construction.SmoothControlPrefix.append_stepCount, hcount, ih, IncidenceSurfaceLength.Construction.card_iteratedBoundaryLabels, Fintype.card_finset]
      exact (ite_eq_left hlevel).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform
