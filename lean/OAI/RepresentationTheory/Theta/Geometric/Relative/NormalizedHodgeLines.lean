import OAI.RepresentationTheory.Theta.Geometric.Relative.FieldTransport
import OAI.RepresentationTheory.Theta.Geometric.Family.NormalizedHodgeLines
import OAI.RepresentationTheory.Theta.Geometric.Normalized.SubmoduleTransport

/-! # Normalized Hodge Lines -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Equality of the actual normalized Hodge lines gives exact transport
of their original distinguished embedding subspaces. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.positivePart_between_of_normalized_eq (τ : E →ₐ[ℚ] ℂ)
    (e₀ : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ)) (z w : D.neighborhood)
    (hline : D.normalizedHodgeLine A ρ s hs hg hdegree τ e₀ z =
      D.normalizedHodgeLine A ρ s hs hg hdegree τ e₀ w) :
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
      (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) s hs hg hdegree τ).map
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (D.coordinateBetween A ρ s hs hg hdegree z w) τ).toLinearMap =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
        (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left) s hs hg hdegree τ :=
  Normalized.SubmoduleTransport.normalizedSubmodule_transport _ _
    (D.transportedNormalizer A ρ s hs hg hdegree τ e₀ z)
    (D.transportedNormalizer A ρ s hs hg hdegree τ e₀ w)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (D.coordinateBetween A ρ s hs hg hdegree z w) τ)
    (D.coordinateBetween_normalizer A ρ s hs hg hdegree τ e₀ z w) hline

end

end OAI.RepresentationTheory.Theta.Geometric
