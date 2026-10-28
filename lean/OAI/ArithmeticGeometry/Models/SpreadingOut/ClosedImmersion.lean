import OAI.ArithmeticGeometry.Models.SpreadingOut.Fg
import OAI.ArithmeticGeometry.Models.SpreadingOut.SchematicClosure
import OAI.ArithmeticGeometry.Models.Foundations
import OAI.ArithmeticGeometry.Models.ModelFiniteness

/-! # Closed Immersion -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.ClosedImmersion.Construction

noncomputable section

/-! Closed subschemes of generic fibers extend by schematic closure in any
finite-presentation coefficient model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

theorem coefficient_generic_preimmersion
    (K : Type u) [Field K] [NumberField K] (s : Finset K) :
    IsPreimmersion (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s) :=
  IsPreimmersion.of_isLocalization (nonZeroDivisors (CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s))

/-- Schematic closure extends a closed immersion without changing the
ambient coefficient model. -/
theorem closed_immersion_has_model
    {K : Type u} [Field K] [NumberField K]
    {W X : Over (Spec (CommRingCat.of K))}
    (i : W ⟶ X) [IsClosedImmersion i.left] (M : Foundations.Constructions.CoefficientModel K X) :
    ∃ (Y : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K M.coefficients))
      (j : Y ⟶ M.model) (p : W.left ⟶ Y.left),
      Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom ∧ IsClosedImmersion j.left ∧
      IsPullback p W.hom Y.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K M.coefficients) ∧
      p ≫ j.left = i.left ≫ M.specialization := by
  have := coefficient_generic_preimmersion K M.coefficients
  have : IsPreimmersion M.specialization :=
    MorphismProperty.of_isPullback M.cartesian.flip inferInstance
  have : QuasiCompact M.specialization :=
    MorphismProperty.of_isPullback M.cartesian.flip inferInstance
  let f := i.left ≫ M.specialization
  let Y : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K M.coefficients) :=
    Over.mk (f.imageι ≫ M.model.hom)
  let j : Y ⟶ M.model := Over.homMk f.imageι rfl
  have hcart : IsPullback f.toImage W.hom Y.hom
      (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K M.coefficients) := by
    have h := (SchematicClosure.Construction.schematicClosure_isPullback i.left M.specialization).flip.paste_vert
      M.cartesian
    rw [i.w] at h
    exact h
  have hfp : Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom := by
    have := ModelFiniteness.Constructions.Foundations.coefficientBase_locallyNoetherian K M.coefficients
    have : LocallyOfFinitePresentation M.model.hom := M.finitePresentation.1
    have : QuasiCompact M.model.hom := M.finitePresentation.2.1
    have : QuasiSeparated M.model.hom := M.finitePresentation.2.2
    change Scheme.Constructions.Foundations.FinitePresentationMorphism (f.imageι ≫ M.model.hom)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  exact ⟨Y, j, f.toImage, hfp,
    inferInstanceAs (IsClosedImmersion f.imageι), hcart, f.toImage_imageι⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.ClosedImmersion.Construction
