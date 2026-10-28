import OAI.RepresentationTheory.Theta.Geometric.Family.EmbeddingIsometry
import OAI.RepresentationTheory.Theta.Geometric.EmbeddedTransportComposition

/-! # Field Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Compare any two fibers in the constructed neighborhood through
their common central transport, preserving the actual Hermitian forms. -/

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

def Intrinsic.CompatibleTransport.NativeCompatibleTransport.coordinateBetween (z w : D.neighborhood) : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E :=
  (D.coordinateTransport A ρ s hs hg hdegree z).symm.trans (D.coordinateTransport A ρ s hs hg hdegree w)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.coordinateBetween_hermitian (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (ξ : E) (hξ : ξ ≠ 0) (z w : D.neighborhood) (v u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian (Family.HermitianTransport.familyHermitianMatrix A ρ hρ (Intrinsic.FamilyFrames.familyChartParameter C w) s hs hg hdegree ξ)
      (D.coordinateBetween A ρ s hs hg hdegree z w v) (D.coordinateBetween A ρ s hs hg hdegree z w u) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian
        (Family.HermitianTransport.familyHermitianMatrix A ρ hρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree ξ) v u := by
  let t := D.coordinateTransport A ρ s hs hg hdegree z
  have hz := D.coordinateTransport_hermitian A ρ hρ s hs hg hdegree z ξ hξ (t.symm v) (t.symm u)
  have hw := D.coordinateTransport_hermitian A ρ hρ s hs hg hdegree w ξ hξ (t.symm v) (t.symm u)
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian
    (Family.HermitianTransport.familyHermitianMatrix A ρ hρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree ξ)
    (t (t.symm v)) (t (t.symm u)) = _ at hz
  rw [t.apply_symm_apply, t.apply_symm_apply] at hz
  exact hw.trans hz.symm

omit [NumberField.IsCMField E] in
theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.coordinateBetween_normalizer (τ : E →ₐ[ℚ] ℂ) (e₀ : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ))
    (z w : D.neighborhood) (v : Fin 3 → ℂ) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (D.coordinateBetween A ρ s hs hg hdegree z w) τ
      (D.transportedNormalizer A ρ s hs hg hdegree τ e₀ z v) =
      D.transportedNormalizer A ρ s hs hg hdegree τ e₀ w v := by
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso ((D.coordinateTransport A ρ s hs hg hdegree z).symm.trans
    (D.coordinateTransport A ρ s hs hg hdegree w)) τ
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (D.coordinateTransport A ρ s hs hg hdegree z) τ (e₀ v)) =
        AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (D.coordinateTransport A ρ s hs hg hdegree w) τ (e₀ v)
  rw [EmbeddedTransportComposition.embeddedLinearIso_trans_apply, EmbeddedTransportComposition.embeddedLinearIso_inverse_apply]

end

end OAI.RepresentationTheory.Theta.Geometric
