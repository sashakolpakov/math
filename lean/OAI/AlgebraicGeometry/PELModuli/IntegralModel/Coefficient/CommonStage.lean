import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.BaseChange

/-! # Common Stage -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.CommonStage.Coefficients

/-! Generalization of the proved CommonStage construction to a general
coefficient ring, for arithmetic parameter spaces of complex schemes.

 Combining independently descended morphisms at one finite coefficient stage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u v w

variable {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K] {s t z : Finset K}

theorem genericModelLift_trans_inv
    {X : Over (Spec (CommRingCat.of K))}
    (X₀ : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)) (p : X.left ⟶ X₀.left)
    (hp : p ≫ X₀.hom = X.hom ≫ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)
    (hst : s ⊆ t) (htz : t ⊆ z) :
    Morphisms.Coefficients.genericModelLift X₀ p hp (hst.trans htz) ≫
        (BaseChange.Coefficients.coefficientBaseChangeTrans hst htz X₀).inv.left =
      Morphisms.Coefficients.genericModelLift ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst)).obj X₀)
        (Morphisms.Coefficients.genericModelLift X₀ p hp hst) (Morphisms.Coefficients.genericModelLift_snd X₀ p hp hst) htz := by
  apply (cancel_mono (BaseChange.Coefficients.coefficientBaseChangeTrans hst htz X₀).hom.left).mp
  erw [Category.assoc, Over.inv_left_hom_left, Category.comp_id, BaseChange.Coefficients.genericModelLift_trans]

noncomputable def descendedMorphismAtLargerBase
    (hst : s ⊆ t) (htz : t ⊆ z)
    {X₀ Y₀ : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)}
    (b : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst)).obj X₀ ⟶
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst)).obj Y₀) :
    (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K (hst.trans htz))).obj X₀ ⟶
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K (hst.trans htz))).obj Y₀ :=
  (BaseChange.Coefficients.coefficientBaseChangeTrans hst htz X₀).inv ≫
    (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K htz)).map b ≫
      (BaseChange.Coefficients.coefficientBaseChangeTrans hst htz Y₀).hom

theorem descendedMorphismAtLargerBase_compatibility
    {X Y : Over (Spec (CommRingCat.of K))}
    (X₀ Y₀ : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s))
    (pX : X.left ⟶ X₀.left) (pY : Y.left ⟶ Y₀.left)
    (hX : pX ≫ X₀.hom = X.hom ≫ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)
    (hY : pY ≫ Y₀.hom = Y.hom ≫ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)
    (a : X ⟶ Y) (hst : s ⊆ t) (htz : t ⊆ z)
    (b : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst)).obj X₀ ⟶
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst)).obj Y₀)
    (hb : Morphisms.Coefficients.genericModelLift X₀ pX hX hst ≫ b.left =
      a.left ≫ Morphisms.Coefficients.genericModelLift Y₀ pY hY hst) :
    Morphisms.Coefficients.genericModelLift X₀ pX hX (hst.trans htz) ≫
        (descendedMorphismAtLargerBase hst htz b).left =
      a.left ≫ Morphisms.Coefficients.genericModelLift Y₀ pY hY (hst.trans htz) := by
  change Morphisms.Coefficients.genericModelLift X₀ pX hX (hst.trans htz) ≫
    ((BaseChange.Coefficients.coefficientBaseChangeTrans hst htz X₀).inv.left ≫
      ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K htz)).map b).left ≫
        (BaseChange.Coefficients.coefficientBaseChangeTrans hst htz Y₀).hom.left) = _
  erw [← Category.assoc, ← Category.assoc, genericModelLift_trans_inv]
  erw [BaseChange.Coefficients.genericModelLift_map _ _ _ _ _ _ a b hb htz, Category.assoc, BaseChange.Coefficients.genericModelLift_trans]
  exact Morphisms.Coefficients.genericModelLift_snd Y₀ pY hY hst

/-- Finitely many generic morphisms between fixed models descend simultaneously. -/
theorem finite_morphisms_descend
    {I : Type v} {E : Type w} [Finite E]
    (src dst : E → I)
    (X : I → Over (Spec (CommRingCat.of K)))
    (X₀ : I → Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s))
    (hX₀ : ∀ i, ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (X₀ i).hom)
    (p : ∀ i, (X i).left ⟶ (X₀ i).left)
    (hp : ∀ i, IsPullback (p i) (X i).hom (X₀ i).hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s))
    (a : ∀ e, X (src e) ⟶ X (dst e)) :
    ∃ (t : Finset K) (h : s ⊆ t)
      (b : ∀ e, (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K h)).obj (X₀ (src e)) ⟶
        (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K h)).obj (X₀ (dst e))),
      ∀ e, Morphisms.Coefficients.genericModelLift (X₀ (src e)) (p (src e)) (hp (src e)).w h ≫ (b e).left =
        (a e).left ≫ Morphisms.Coefficients.genericModelLift (X₀ (dst e)) (p (dst e)) (hp (dst e)).w h := by
  classical
  let : Fintype E := Fintype.ofFinite E
  choose t ht b hb using fun e ↦ Morphisms.Coefficients.morphism_between_models_descends
    (X₀ (src e)) (X₀ (dst e)) (hX₀ (src e)) (hX₀ (dst e))
    (p (src e)) (p (dst e)) (hp (src e)) (hp (dst e)) (a e)
  let z := s ∪ Finset.univ.biUnion t
  have htz (e : E) : t e ⊆ z :=
    (Finset.subset_biUnion_of_mem t (Finset.mem_univ e)).trans Finset.subset_union_right
  refine ⟨z, Finset.subset_union_left,
    (fun e ↦ descendedMorphismAtLargerBase (ht e) (htz e) (b e)), ?_⟩
  intro e
  exact descendedMorphismAtLargerBase_compatibility
    (X₀ (src e)) (X₀ (dst e)) (p (src e)) (p (dst e)) (hp (src e)).w (hp (dst e)).w
    (a e) (ht e) (htz e) (b e) (hb e)

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.CommonStage.Coefficients
