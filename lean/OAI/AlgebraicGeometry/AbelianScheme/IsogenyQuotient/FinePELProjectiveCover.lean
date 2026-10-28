import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELComplexOpenDetection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Fine PEL Projective Cover -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELProjectiveCover.Construction

noncomputable section

/-! ReferenceFamily's original projective component inclusions cover the entire
complex fine PEL scheme. The resulting actual open cover makes that
scheme locally Noetherian without adding any Noetherian premise. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
theorem finePEL_complex_locallyNoetherian_of_projective_components
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} [NeZero N]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K} (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine)
    (κ : K →+* ℂ) (hC : Z.HasProjectiveBallComponents κ) :
    IsLocallyNoetherian (Z.complexFiber κ).left := by
  have h : ∀ C : Z.ComplexComponent κ, ∃ (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
      (f : X.toOver ⟶ Z.complexFiber κ), IsOpenImmersion f.left ∧
        IsLocallyNoetherian X.toOver.left ∧
        Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) = {x | ConnectedComponents.mk x = C} := by
    intro C
    obtain ⟨X, ⟨_, f, hf, _, hr⟩, _⟩ := hC C
    exact ⟨X, f, hf, inferInstanceAs (IsLocallyNoetherian X.presentation.carrier), hr⟩
  choose X f hf hN hr using h
  have (C : Z.ComplexComponent κ) : IsOpenImmersion (f C).left := hf C
  let U : (Z.complexFiber κ).left.Opens := ⨆ C, (f C).left.opensRange
  have hU : U = ⊤ := PELComplexOpenDetection.Construction.finePEL_complex_open_eq_top_of_complex_points Z hZ κ U (by
    intro p
    let C : Z.ComplexComponent κ := ConnectedComponents.mk p
    have hp : p ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (f C)) := by rw [hr C]; rfl
    obtain ⟨a, ha⟩ := hp
    apply (le_iSup (fun C => (f C).left.opensRange) C)
    exact ⟨a.left (IsLocalRing.closedPoint ℂ), congrArg (fun q => q.left (IsLocalRing.closedPoint ℂ)) ha⟩)
  have hcover : ∀ z : (Z.complexFiber κ).left, ∃ C y, (f C).left y = z := by
    intro z
    have hz : z ∈ U := (congrArg (fun V : (Z.complexFiber κ).left.Opens => z ∈ V) hU).mpr trivial
    change z ∈ ⨆ C, (f C).left.opensRange at hz
    simpa only [TopologicalSpace.Opens.mem_iSup, Scheme.Hom.mem_opensRange] using hz
  let cover : (Z.complexFiber κ).left.OpenCover :=
    Scheme.Cover.mkOfCovers (Z.ComplexComponent κ) (fun C => (X C).toOver.left)
      (fun C => (f C).left) hcover hf
  exact (isLocallyNoetherian_iff_openCover cover).mpr hN

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELProjectiveCover.Construction
