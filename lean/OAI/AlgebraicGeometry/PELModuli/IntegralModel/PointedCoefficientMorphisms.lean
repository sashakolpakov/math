import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GenericMorphisms
import OAI.ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness

/-! # Pointed Coefficient Morphisms -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedCoefficientMorphisms.Coefficients

noncomputable section

/-! Descent of the actual pointed source map to a finite coefficient
stage. The pointed equation is proved by generic faithfulness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

open OAI.ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness.Construction

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {s : Finset K}

theorem generic_morphism_descends
    (M N : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s))
    (hM : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism M.hom) (hN : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism N.hom)
    (a : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).obj M ⟶
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).obj N) :
    ∃ (t : Finset K) (h : s ⊆ t)
      (b : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj M ⟶
        (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj N),
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)).map b ≫
        ((Coefficient.GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := R) h).app N).hom =
        ((Coefficient.GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := R) h).app M).hom ≫ a := by
  let models : Bool → Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s) := fun j => cond j N M
  have hmodels (j : Bool) : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (models j).hom := by
    cases j
    · exact hM
    · exact hN
  obtain ⟨t, h, b, hb⟩ := Coefficient.GenericMorphisms.Coefficients.finite_generic_morphisms_descend models hmodels
    (fun _ : Unit => false) (fun _ => true) (fun _ => a)
  exact ⟨t, h, b (), hb ()⟩

/-- Pointedness holds over the constructed coefficient ring itself. -/
theorem pointed_generic_morphism_descends
    (M N : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) [Smooth M.hom] [IsProper M.hom]
    [Smooth N.hom] [IsProper N.hom]
    (x₀ : 𝟙_ (Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) ⟶ M)
    (y₀ : 𝟙_ (Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) ⟶ N)
    (a : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).obj M ⟶
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).obj N)
    (ha : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).map x₀ ≫ a =
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).map y₀) :
    ∃ (t : Finset K) (h : s ⊆ t)
      (b : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj M ⟶
        (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj N),
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).map x₀ ≫ b =
        (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).map y₀ ∧
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)).map b ≫
        ((Coefficient.GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := R) h).app N).hom =
        ((Coefficient.GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := R) h).app M).hom ≫ a := by
  obtain ⟨t, h, b, hb⟩ := generic_morphism_descends M N
    ⟨inferInstance, inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance, inferInstance⟩ a
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)
  let G := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)
  let H := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)
  let c := Coefficient.GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := R) h
  have : Smooth (F.obj (𝟙_ (Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)))).hom :=
    inferInstanceAs (Smooth (pullback.snd (𝟙 _) _))
  have : IsProper (F.obj N).hom := inferInstanceAs (IsProper (pullback.snd N.hom _))
  have hinj : Function.Injective (G.map : (F.obj (𝟙_ _) ⟶ F.obj N) → _) :=
    ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness.Construction.generic_pullback_map_injective (algebraMap (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K t) K) Subtype.val_injective
  have hx : G.map (F.map x₀) ≫ (c.app M).hom = (c.app (𝟙_ _)).hom ≫ H.map x₀ :=
    c.hom.naturality x₀
  have hy : G.map (F.map y₀) ≫ (c.app N).hom = (c.app (𝟙_ _)).hom ≫ H.map y₀ :=
    c.hom.naturality y₀
  change G.map b ≫ (c.app N).hom = (c.app M).hom ≫ a at hb
  change H.map x₀ ≫ a = H.map y₀ at ha
  refine ⟨t, h, b, hinj ?_, hb⟩
  apply (cancel_mono (c.app N).hom).mp
  rw [G.map_comp, Category.assoc, hb, ← Category.assoc,
    hx, Category.assoc, ha]
  exact hy.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedCoefficientMorphisms.Coefficients
