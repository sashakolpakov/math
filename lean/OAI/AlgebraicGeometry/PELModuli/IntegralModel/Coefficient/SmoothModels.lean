import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.FractionField
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Finiteness
import OAI.ArithmeticGeometry.Models.SpreadingOut.CoefficientSmoothness

/-! # Smooth Models -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.SmoothModels.Coefficients

noncomputable section

/-! Smoothness of a proper ambient-field fiber extends after inverting
one coefficient. The ambient field need not be the fraction field of the
coefficient ring: smoothness first descends to that actual fraction field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R K : Type} [CommRing R] [IsNoetherianRing R] [Field K] [Algebra R K]

omit [IsNoetherianRing R] in
theorem coefficient_base_in_basicOpen {s : Finset K}
    (a : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) (ha : a ≠ 0) :
    ∃ (t : Finset K) (h : s ⊆ t),
      Set.range (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h) ⊆
        ((show (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s).Opens from PrimeSpectrum.basicOpen a) :
          Set (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) := by
  classical
  let t := insert (a.val⁻¹) s
  have h : s ⊆ t := Finset.subset_insert _ _
  let φ : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s →+* ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K t :=
    ((ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientDiagram R K).map (homOfLE h)).hom
  have hn : (φ a : K) ≠ 0 := fun hn => ha (Subtype.ext hn)
  have hi : (φ a : K)⁻¹ ∈ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K t :=
    Algebra.subset_adjoin (Finset.mem_insert_self _ _)
  have hu : IsUnit (φ a) := ArithmeticGeometry.Models.SpreadingOut.CoefficientSmoothness.Construction.subalgebra_unit_of_inverse_mem
    (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K t) (φ a) hn hi
  exact ⟨t, h, ArithmeticGeometry.Models.SpreadingOut.CoefficientSmoothness.Construction.specMap_range_subset_basicOpen_of_unit φ a hu⟩

theorem proper_model_eventually_smooth {s : Finset K}
    (M : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) [IsProper M.hom]
    [Smooth ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).obj M).hom] :
    ∃ (t : Finset K) (h : s ⊆ t),
      Smooth ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj M).hom ∧
        IsProper ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj M).hom := by
  have : IsLocallyNoetherian (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s) := Finiteness.Coefficients.coefficientBase_locallyNoetherian R K s
  let D : Models.Coefficients.CoefficientModel R K ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).obj M) := {
    coefficients := s
    model := M
    finitePresentation := ⟨inferInstance, inferInstance, inferInstance⟩
    genericIso := Iso.refl _ }
  have hsm : Smooth ((Over.pullback (FractionField.Coefficients.fractionBaseMap R K s)).obj M).hom := D.smooth_fractionFiber
  have : Smooth (CategoryTheory.Limits.pullback.snd M.hom
      (Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) (FractionField.Coefficients.coefficientFractionField R K s))))) := hsm
  obtain ⟨a, ha, hsmOpen⟩ := ArithmeticGeometry.Models.SpreadingOut.CoefficientSmoothness.Construction.proper_smooth_generic_fiber_has_smooth_basicOpen
    (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) (FractionField.Coefficients.coefficientFractionField R K s) M.hom
  obtain ⟨t, h, ht⟩ := coefficient_base_in_basicOpen a ha
  have := hsmOpen
  exact ⟨t, h, ArithmeticGeometry.Models.SpreadingOut.CoefficientSmoothness.Construction.smooth_pullback_of_range_subset M.hom
    (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h) (PrimeSpectrum.basicOpen a) ht,
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd M.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)))⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.SmoothModels.Coefficients
