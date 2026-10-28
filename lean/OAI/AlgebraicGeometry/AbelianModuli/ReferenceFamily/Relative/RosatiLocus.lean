import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.RosatiBasisPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveFixedEquationLocus

/-! # Rosati Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.RosatiLocus

noncomputable section

/-! The original Rosati condition on a projectively presented polarized
abelian family over a noetherian base has a closed locus classifying
all test schemes, including arbitrary nonreduced tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_projective_relative_rosati_locus
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Scheme.{0}} [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A.abelian.scheme)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian) :
    ∃ Z : Over S, IsClosedImmersion Z.hom ∧
      ActionData.RosatiConjugation (A.pullback Z.hom) (ρ.pullback Z.hom) ∧
      ∀ (T : Over S),
        ActionData.RosatiConjugation (A.pullback T.hom) (ρ.pullback T.hom) ↔
          ∃! _f : T ⟶ Z, True := by
  let l (i : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E))) :=
    A.polarization.isogeny.hom ≫ Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback A.dual A.dual (ρ.map (PELModuli.IntegralModel.Finite.Actions.integralActionBasis E i))
  let r (i : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E))) :=
    ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E (PELModuli.IntegralModel.Finite.Actions.integralActionBasis E i)) ≫
      A.polarization.isogeny.hom
  obtain ⟨Z, hZ, hU, hclass⟩ := ProjectiveFixedEquationLocus.exists_projective_fixed_pullback_equation_locus B l r
  exact ⟨Z, hZ, (RosatiBasisPullback.rosati_iff_relative_pulledBack_basis_equations A ρ Z.hom).mpr hU,
    fun T => (RosatiBasisPullback.rosati_iff_relative_pulledBack_basis_equations A ρ T.hom).trans (hclass T)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.RosatiLocus
