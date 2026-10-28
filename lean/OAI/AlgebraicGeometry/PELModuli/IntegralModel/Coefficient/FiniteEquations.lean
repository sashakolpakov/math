import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.BaseChange

/-! # Finite Equations -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.FiniteEquations.Coefficients

/-! Generalization of the proved FiniteEquations construction to a general
coefficient ring, for arithmetic parameter spaces of complex schemes.

 Simultaneous preservation of finitely many generic equations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u v w

variable {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K] {s t z : Finset K}

theorem equation_survives_enlargement
    (hst : s ⊆ t) (htz : t ⊆ z)
    (X₀ Y₀ : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)) (a b : X₀ ⟶ Y₀)
    (hab : pullback.fst X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst) ≫ a.left =
      pullback.fst X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst) ≫ b.left) :
    pullback.fst X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K (hst.trans htz)) ≫ a.left =
      pullback.fst X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K (hst.trans htz)) ≫ b.left := by
  let : Epi (BaseChange.Coefficients.coefficientBaseChangeTrans hst htz X₀).hom.left := by
    change Epi (BaseChange.Coefficients.coefficientBaseChangeTransSquare hst htz X₀).isoPullback.hom
    infer_instance
  apply (cancel_epi (BaseChange.Coefficients.coefficientBaseChangeTrans hst htz X₀).hom.left).mp
  erw [← Category.assoc, BaseChange.Coefficients.coefficientBaseChangeTrans_hom_fst,
    ← Category.assoc, BaseChange.Coefficients.coefficientBaseChangeTrans_hom_fst, Category.assoc, Category.assoc, hab]

theorem baseChange_map_eq_of_fst_eq
    (hst : s ⊆ t) (X₀ Y₀ : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)) (a b : X₀ ⟶ Y₀)
    (hab : pullback.fst X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst) ≫ a.left =
      pullback.fst X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst) ≫ b.left) :
    (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst)).map a =
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst)).map b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · erw [pullback.lift_fst, pullback.lift_fst]
    exact hab
  · erw [pullback.lift_snd, pullback.lift_snd]

/-- Finitely many equations holding on the generic fiber hold at one common stage. -/
theorem finite_equations_descend
    {I : Type v} {E : Type w} [Finite E]
    (src dst : E → I)
    (X : I → Over (Spec (CommRingCat.of K)))
    (X₀ : I → Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s))
    (hX₀ : ∀ i, ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (X₀ i).hom)
    (p : ∀ i, (X i).left ⟶ (X₀ i).left)
    (hp : ∀ i, IsPullback (p i) (X i).hom (X₀ i).hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s))
    (a b : ∀ e, X₀ (src e) ⟶ X₀ (dst e))
    (hab : ∀ e, p (src e) ≫ (a e).left = p (src e) ≫ (b e).left) :
    ∃ (t : Finset K) (hst : s ⊆ t),
      ∀ e, (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst)).map (a e) =
        (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst)).map (b e) := by
  classical
  let : Fintype E := Fintype.ofFinite E
  choose t ht heq using fun e ↦ Morphisms.Coefficients.equation_between_models_descends
    (X₀ (src e)) (X₀ (dst e)) (hX₀ (src e)) (hX₀ (dst e))
    (p (src e)) (hp (src e)) (a e) (b e) (hab e)
  let z := s ∪ Finset.univ.biUnion t
  have htz (e : E) : t e ⊆ z :=
    (Finset.subset_biUnion_of_mem t (Finset.mem_univ e)).trans Finset.subset_union_right
  refine ⟨z, Finset.subset_union_left, fun e ↦ ?_⟩
  apply baseChange_map_eq_of_fst_eq
  exact equation_survives_enlargement (ht e) (htz e) (X₀ (src e)) (X₀ (dst e))
    (a e) (b e) (heq e)

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.FiniteEquations.Coefficients
