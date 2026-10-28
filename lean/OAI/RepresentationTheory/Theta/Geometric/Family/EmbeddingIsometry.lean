import OAI.RepresentationTheory.Theta.Geometric.Family.HermitianTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.IsometryEmbedding

/-! # Embedding Isometry -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The constructed field transport is an isometry at every embedding;
it carries one fixed central normalizer to normalizers of all nearby fibers. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

def Intrinsic.CompatibleTransport.NativeCompatibleTransport.transportedNormalizer (τ : E →ₐ[ℚ] ℂ) (e₀ : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ))
    (z : D.neighborhood) : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ) :=
  e₀.trans (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (D.coordinateTransport A ρ s hs hg hdegree z) τ)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.coordinateTransport_embedding_isometry (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (z : D.neighborhood) (ξ : E) (hξ : ξ ≠ 0) (τ : E →ₐ[ℚ] ℂ) (v w : Fin 3 → ℂ) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm
      ((Family.HermitianTransport.familyHermitianMatrix A ρ hρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree ξ).map τ)
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (D.coordinateTransport A ρ s hs hg hdegree z) τ v)
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (D.coordinateTransport A ρ s hs hg hdegree z) τ w) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm
        ((Family.HermitianTransport.familyHermitianMatrix A ρ hρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree ξ).map τ) v w :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.IsometryEmbedding.hermitianIsometry_embedding _ _ (D.coordinateTransport A ρ s hs hg hdegree z).toLinearMap
    (D.coordinateTransport_hermitian A ρ hρ s hs hg hdegree z ξ hξ) τ v w

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.transportedNormalizer_isometry (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (ξ : E) (hξ : ξ ≠ 0) (τ : E →ₐ[ℚ] ℂ)
    (e₀ : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ)) (Q : Matrix (Fin 3) (Fin 3) ℂ)
    (he₀ : ∀ v w, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm
      ((Family.HermitianTransport.familyHermitianMatrix A ρ hρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree ξ).map τ)
      (e₀ v) (e₀ w) = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm Q v w)
    (z : D.neighborhood) (v w : Fin 3 → ℂ) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm
      ((Family.HermitianTransport.familyHermitianMatrix A ρ hρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree ξ).map τ)
      (D.transportedNormalizer A ρ s hs hg hdegree τ e₀ z v)
      (D.transportedNormalizer A ρ s hs hg hdegree τ e₀ z w) = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm Q v w :=
  (D.coordinateTransport_embedding_isometry A ρ s hs hg hdegree hρ z ξ hξ τ (e₀ v) (e₀ w)).trans (he₀ v w)

end

end OAI.RepresentationTheory.Theta.Geometric
