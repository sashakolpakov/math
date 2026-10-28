import OAI.RepresentationTheory.Theta.Geometric.Family.HermitianTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine

/-! # Central Normalizer -/

namespace OAI.RepresentationTheory.Theta.Geometric.Family.CentralNormalizer

noncomputable section

/-! Construct an actual Hermitian normalizer from the original Rosati
polarization and the prescribed rank-two tangent eigenspace. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

theorem exists_familyHermitian_normalizer (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s)
    (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (ξ : E) (hξ : ξ ≠ 0) (hconj : AlgebraicGeometry.ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ)
    (τ : E →ₐ[ℚ] ℂ) (him : 0 < (τ ξ).im) (b : E)
    (hb : AlgebraicGeometry.ComplexMultiplication.CM.TraceForm.cmFieldConjugation E b = b) (hbneg : (τ b).re < 0)
    (hr : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.abelian.pullback y.left) (ρ.pullback y.left)
      (τ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) 2) :
    ∃ e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec, ∀ v w,
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm ((HermitianTransport.familyHermitianMatrix A ρ hρ y s hs hg hdegree ξ).map τ) (e v) (e w) =
        AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, τ b]) v w := by
  obtain ⟨e, he⟩ := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianNormalizer.IntrinsicHermitianMarking.exists_nativeHermitian_normalizer (A.pullback y.left) (ρ.pullback y.left)
    s hs hg hdegree τ (hρ.pullback A ρ y.left) ξ hξ hconj him hr b hb hbneg
  exact ⟨e, fun v w => (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply _ _ _).trans
    ((he v w).trans (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine.complexMatrixHermitian_diagonal τ.toRingHom b v w))⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Family.CentralNormalizer
