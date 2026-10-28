import OAI.Analysis.PDE.Concentration.Physical.Current
import OAI.Analysis.PDE.Green.Physical.FullProjection

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

@[simp] theorem nullIndexEquiv_symm_none (d : ℕ) :
    (nullIndexEquiv d).symm none = 0 :=
  (nullIndexEquiv d).symm_apply_eq.mpr (nullIndexEquiv_zero d).symm

@[simp] theorem nullIndexEquiv_symm_some_none (d : ℕ) :
    (nullIndexEquiv d).symm (some none) = 1 :=
  (nullIndexEquiv d).symm_apply_eq.mpr (nullIndexEquiv_one d).symm

@[simp] theorem nullIndexEquiv_symm_some_some (d : ℕ) (i : Fin d) :
    (nullIndexEquiv d).symm (some (some i)) = i.succ.succ :=
  (nullIndexEquiv d).symm_apply_eq.mpr (nullIndexEquiv_transverse d i).symm

/-- The complex variables in the rotated packet current are exactly the
physical fiber embedding, not a separately chosen coordinate model. -/
theorem physicalToNullCurrentPoint_imaginary (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    (physicalToNullCurrentPoint d x).2 =
      OAI.Analysis.Calculus.Current.physicalEmbedding (OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1 (OAI.Analysis.PDE.Green.fullPhysicalProjection d x).2 := by
  funext i
  change (nullCoordinateProjection d
    (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift (nullRotation d)) x)).2 i = _
  rw [nullCoordinateProjection_imaginary]
  cases i with
  | none =>
    simp only [nullIndexEquiv_symm_none, nullRotation_action_time]
    apply Complex.ext <;>
      simp [OAI.Analysis.Calculus.Current.physicalEmbedding, OAI.Analysis.Calculus.Current.physicalLift, OAI.Analysis.Calculus.Current.physicalTimeOffset, OAI.Analysis.PDE.Green.fullPhysicalProjection,
        Complex.real_smul, div_eq_mul_inv] <;> ring
  | some i =>
    cases i with
    | none =>
      simp only [nullIndexEquiv_symm_some_none, nullRotation_action_longitudinal]
      apply Complex.ext <;>
        simp [OAI.Analysis.Calculus.Current.physicalEmbedding, OAI.Analysis.Calculus.Current.physicalLift, OAI.Analysis.Calculus.Current.physicalTimeOffset, OAI.Analysis.PDE.Green.fullPhysicalProjection,
          Complex.real_smul, div_eq_mul_inv] <;> ring
    | some i =>
      simp [nullIndexEquiv_symm_some_some, nullRotation_action_transverse,
        OAI.Analysis.Calculus.Current.physicalEmbedding, OAI.Analysis.Calculus.Current.physicalLift, OAI.Analysis.Calculus.Current.physicalTimeOffset, OAI.Analysis.PDE.Green.fullPhysicalProjection]

theorem imaginaryTime_physicalToNullCurrentPoint (d : ℕ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    OAI.Analysis.Calculus.Current.imaginaryTime (physicalToNullCurrentPoint d x).2 = (OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1 := by
  rw [physicalToNullCurrentPoint_imaginary, OAI.Analysis.Calculus.Current.imaginaryTime_physicalEmbedding]

end OAI.Analysis.PDE.Concentration
