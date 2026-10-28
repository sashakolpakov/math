import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Finite Generators -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteGenerators.Realization

noncomputable section

/-! Concrete finite-adelic generator formulas from PoissonAutomorphy's rational splitting. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

def adelicAtFinite (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) : ι → Theta.PoissonAutomorphyNormalizationData.AQ := fun i => (0, x i)

omit [DecidableEq ι] in
theorem rational_matrix_at_finite (M : Matrix ι ι ℚ) (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    M.map (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQ) *ᵥ adelicAtFinite x =
      adelicAtFinite (M.map (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) *ᵥ x) := by
  funext i
  apply Prod.ext <;> simp [adelicAtFinite, Matrix.mulVec, dotProduct, Prod.fst_sum, Prod.snd_sum]

theorem finiteAction_from_rational_at_zero (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) (φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (D.finiteAction γ φ).val x = Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (Theta.PoissonAutomorphyNormalizationData.toSiegel (Theta.PoissonAutomorphyNormalizationData.basePeriod ι)) *
      (D.rationalAction γ (Theta.PoissonAutomorphyNormalizationData.tensor D.vacuum φ)).val (adelicAtFinite x) := by
  have h := congrArg (fun F : Theta.PoissonAutomorphyNormalizationData.adelicSchwartz ι => F.val (adelicAtFinite x))
    (D.rationalAction_tensor γ D.vacuum φ)
  change (D.rationalAction γ (Theta.PoissonAutomorphyNormalizationData.tensor D.vacuum φ)).val (adelicAtFinite x) =
    (D.real.action (D.normalizedRealLift γ) D.vacuum).val 0 * (D.finiteAction γ φ).val x at h
  rw [D.normalizedRealLift_coefficient] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (Theta.PoissonAutomorphyNormalizationData.halfDet_ne_zero _ _), one_mul]

/-- This is the actual finite action selected by PoissonAutomorphy's normalized real lift.
Its scalar is derived by evaluating the global rational action at real zero. -/
theorem finiteAction_rational_linear (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) (A : (Matrix ι ι ℚ)ˣ)
    (hγ : γ.val = Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose)
    (φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (D.finiteAction γ φ).val x = Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (Theta.PoissonAutomorphyNormalizationData.toSiegel (Theta.PoissonAutomorphyNormalizationData.basePeriod ι)) *
      φ.val (A.val.transpose.map (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) *ᵥ x) := by
  rw [finiteAction_from_rational_at_zero]
  change _ * (D.adelic.action (D.rationalSplit γ) (Theta.PoissonAutomorphyNormalizationData.tensor D.vacuum φ)).val (adelicAtFinite x) = _
  rw [D.rational_linear γ A hγ, rational_matrix_at_finite]
  change _ * (D.vacuum.val 0 * φ.val _) = _
  rw [D.vacuum_eq]
  simp [adelicAtFinite]

omit [DecidableEq ι] in
theorem finite_quadratic_at_finite (B : Matrix ι ι ℚ) (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQ (1 / 2) *
        (adelicAtFinite x ⬝ᵥ (B.map (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQ) *ᵥ adelicAtFinite x)) =
      (0, algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * (x ⬝ᵥ (B.map (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) *ᵥ x))) := by
  rw [rational_matrix_at_finite]
  apply Prod.ext <;>
    simp [adelicAtFinite, dotProduct, Prod.fst_sum, Prod.snd_sum]

theorem finiteAction_rational_quadratic (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) (B : Matrix ι ι ℚ) (hB : B.IsSymm)
    (hγ : γ.val = Matrix.fromBlocks 1 B 0 1)
    (φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (D.finiteAction γ φ).val x = Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (Theta.PoissonAutomorphyNormalizationData.toSiegel (Theta.PoissonAutomorphyNormalizationData.basePeriod ι)) *
      (D.finiteCharacter (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) *
        (x ⬝ᵥ (B.map (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) *ᵥ x))) * φ.val x) := by
  rw [finiteAction_from_rational_at_zero]
  change _ * (D.adelic.action (D.rationalSplit γ) (Theta.PoissonAutomorphyNormalizationData.tensor D.vacuum φ)).val (adelicAtFinite x) = _
  rw [D.rational_quadratic γ B hB hγ, finite_quadratic_at_finite, ← D.finiteCharacter_eq]
  change _ * (_ * (D.vacuum.val 0 * φ.val (fun i => (adelicAtFinite x i).2))) = _
  rw [D.vacuum_eq]
  simp [adelicAtFinite]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteGenerators.Realization
