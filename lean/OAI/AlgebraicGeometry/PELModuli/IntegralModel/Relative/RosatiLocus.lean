import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.RosatiBasisPullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEquationLocus

/-! # Rosati Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.RosatiLocus

noncomputable section

/-! The original Rosati condition on a varying reduced noetherian
polarized abelian family has an actual reduced closed locus. It is
constructed from smooth-source equalizers and classifies all reduced tests. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_reduced_relative_rosati_locus
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Scheme.{0}} [IsReduced S] [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian) :
    ∃ Z : Over S, IsReduced Z.left ∧ IsClosedImmersion Z.hom ∧
      AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback Z.hom) (ρ.pullback Z.hom) ∧
      ∀ (T : Over S) [IsReduced T.left],
        AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) (ρ.pullback T.hom) ↔
          ∃! _f : T ⟶ Z, True := by
  let l (i : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E))) :=
    A.polarization.isogeny.hom ≫ Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback A.dual A.dual (ρ.map (Finite.Actions.integralActionBasis E i))
  let r (i : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E))) :=
    ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E (Finite.Actions.integralActionBasis E i)) ≫
      A.polarization.isogeny.hom
  obtain ⟨Z, hred, hZ, hU, hclass⟩ := SmoothEquationLocus.exists_reduced_smooth_equation_locus l r
  exact ⟨Z, hred, hZ, (RosatiBasisPullback.rosati_iff_relative_pulledBack_basis_equations A ρ Z.hom).mpr hU,
    fun T _ => (RosatiBasisPullback.rosati_iff_relative_pulledBack_basis_equations A ρ T.hom).trans (hclass T)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.RosatiLocus
