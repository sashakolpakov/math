import OAI.RepresentationTheory.Theta.Geometric.Family.EmbeddingIsometry
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine

/-! # Normalized Hodge Lines -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! One central normalizer, transported by the actual common frame,
gives a unique negative ball line for every nearby rank-two PEL fiber. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

def Intrinsic.CompatibleTransport.NativeCompatibleTransport.normalizedHodgeLine (τ : E →ₐ[ℚ] ℂ) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z : D.neighborhood) : Submodule ℂ Geometry.ComplexBall.PrescribedSignsB.Vec :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine.NativeHermitianMarking.nativeNormalizedHodgeLine (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
    (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) s hs hg hdegree τ
    (D.transportedNormalizer A ρ s hs hg hdegree τ e₀ z)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.transportedNormalizer_diagonal (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (ξ : E) (hξ : ξ ≠ 0) (τ : E →ₐ[ℚ] ℂ) (b : E) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (he₀ : ∀ v w, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm
      ((Family.HermitianTransport.familyHermitianMatrix A ρ hρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree ξ).map τ)
      (e₀ v) (e₀ w) = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, τ b]) v w)
    (z : D.neighborhood) (v w : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian τ.toRingHom
      (Family.HermitianTransport.familyHermitianMatrix A ρ hρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree ξ)
      (D.transportedNormalizer A ρ s hs hg hdegree τ e₀ z v)
      (D.transportedNormalizer A ρ s hs hg hdegree τ e₀ z w) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian τ.toRingHom (Matrix.diagonal ![1, 1, b]) v w :=
  (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply _ _ _).symm.trans
    ((D.transportedNormalizer_isometry A ρ s hs hg hdegree hρ ξ hξ τ e₀ _ he₀ z v w).trans
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine.complexMatrixHermitian_diagonal τ.toRingHom b v w).symm)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.exists_normalizedHodge_ball_coordinate (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (ξ : E) (hξ : ξ ≠ 0) (hconj : AlgebraicGeometry.ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ)
    (τ : E →ₐ[ℚ] ℂ) (him : 0 < (τ ξ).im) (b : E) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (he₀ : ∀ v w, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm
      ((Family.HermitianTransport.familyHermitianMatrix A ρ hρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree ξ).map τ)
      (e₀ v) (e₀ w) = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, τ b]) v w)
    (z : D.neighborhood)
    (hr : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
      (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
      (τ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) 2) :
    ∃! w : Geometry.ComplexBall.PrescribedSignsB.BallChart, D.normalizedHodgeLine A ρ s hs hg hdegree τ e₀ z = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w} ∧
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, τ b]) (Geometry.ComplexBall.PrescribedSignsB.lineVector w) (Geometry.ComplexBall.PrescribedSignsB.lineVector w)).re < 0 :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine.NativeHermitianMarking.exists_unique_nativeHodge_ball_coordinate
    (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
    s hs hg hdegree τ (D.transportedNormalizer A ρ s hs hg hdegree τ e₀ z)
    (hρ.pullback A ρ (Intrinsic.FamilyFrames.familyChartParameter C z).left) ξ hξ hconj him b
    (D.transportedNormalizer_diagonal A ρ s hs hg hdegree hρ ξ hξ τ b e₀ he₀ z) hr

end

end OAI.RepresentationTheory.Theta.Geometric
