import OAI.ArithmeticGeometry.Models.BaseChange

/-! # Common Stage -/

namespace OAI.ArithmeticGeometry.Models.CommonStage.Constructions.Foundations

/-! Combining independently descended morphisms at one finite coefficient stage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u v w

variable {K : Type u} [Field K] {s t z : Finset K}

theorem genericModelLift_trans_inv
    {X : Over (Spec (CommRingCat.of K))}
    (X₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) (p : X.left ⟶ X₀.left)
    (hp : p ≫ X₀.hom = X.hom ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
    (hst : s ⊆ t) (htz : t ⊆ z) :
    ModelMorphisms.Constructions.Foundations.genericModelLift X₀ p hp (hst.trans htz) ≫
        (BaseChange.Constructions.Foundations.coefficientBaseChangeTrans hst htz X₀).inv.left =
      ModelMorphisms.Constructions.Foundations.genericModelLift ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)).obj X₀)
        (ModelMorphisms.Constructions.Foundations.genericModelLift X₀ p hp hst) (ModelMorphisms.Constructions.Foundations.genericModelLift_snd X₀ p hp hst) htz := by
  apply (cancel_mono (BaseChange.Constructions.Foundations.coefficientBaseChangeTrans hst htz X₀).hom.left).mp
  erw [Category.assoc, Over.inv_left_hom_left, Category.comp_id, BaseChange.Constructions.Foundations.genericModelLift_trans]

noncomputable def descendedMorphismAtLargerBase
    (hst : s ⊆ t) (htz : t ⊆ z)
    {X₀ Y₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)}
    (b : (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)).obj X₀ ⟶
      (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)).obj Y₀) :
    (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K (hst.trans htz))).obj X₀ ⟶
      (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K (hst.trans htz))).obj Y₀ :=
  (BaseChange.Constructions.Foundations.coefficientBaseChangeTrans hst htz X₀).inv ≫
    (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K htz)).map b ≫
      (BaseChange.Constructions.Foundations.coefficientBaseChangeTrans hst htz Y₀).hom

theorem descendedMorphismAtLargerBase_compatibility
    {X Y : Over (Spec (CommRingCat.of K))}
    (X₀ Y₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
    (pX : X.left ⟶ X₀.left) (pY : Y.left ⟶ Y₀.left)
    (hX : pX ≫ X₀.hom = X.hom ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
    (hY : pY ≫ Y₀.hom = Y.hom ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
    (a : X ⟶ Y) (hst : s ⊆ t) (htz : t ⊆ z)
    (b : (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)).obj X₀ ⟶
      (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)).obj Y₀)
    (hb : ModelMorphisms.Constructions.Foundations.genericModelLift X₀ pX hX hst ≫ b.left =
      a.left ≫ ModelMorphisms.Constructions.Foundations.genericModelLift Y₀ pY hY hst) :
    ModelMorphisms.Constructions.Foundations.genericModelLift X₀ pX hX (hst.trans htz) ≫
        (descendedMorphismAtLargerBase hst htz b).left =
      a.left ≫ ModelMorphisms.Constructions.Foundations.genericModelLift Y₀ pY hY (hst.trans htz) := by
  change ModelMorphisms.Constructions.Foundations.genericModelLift X₀ pX hX (hst.trans htz) ≫
    ((BaseChange.Constructions.Foundations.coefficientBaseChangeTrans hst htz X₀).inv.left ≫
      ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K htz)).map b).left ≫
        (BaseChange.Constructions.Foundations.coefficientBaseChangeTrans hst htz Y₀).hom.left) = _
  erw [← Category.assoc, ← Category.assoc, genericModelLift_trans_inv]
  erw [BaseChange.Constructions.Foundations.genericModelLift_map _ _ _ _ _ _ a b hb htz, Category.assoc, BaseChange.Constructions.Foundations.genericModelLift_trans]
  exact ModelMorphisms.Constructions.Foundations.genericModelLift_snd Y₀ pY hY hst

/-- Finitely many generic morphisms between fixed models descend simultaneously. -/
theorem finite_morphisms_descend
    {I : Type v} {E : Type w} [Finite E]
    (src dst : E → I)
    (X : I → Over (Spec (CommRingCat.of K)))
    (X₀ : I → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
    (hX₀ : ∀ i, Scheme.Constructions.Foundations.FinitePresentationMorphism (X₀ i).hom)
    (p : ∀ i, (X i).left ⟶ (X₀ i).left)
    (hp : ∀ i, IsPullback (p i) (X i).hom (X₀ i).hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s))
    (a : ∀ e, X (src e) ⟶ X (dst e)) :
    ∃ (t : Finset K) (h : s ⊆ t)
      (b : ∀ e, (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj (X₀ (src e)) ⟶
        (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj (X₀ (dst e))),
      ∀ e, ModelMorphisms.Constructions.Foundations.genericModelLift (X₀ (src e)) (p (src e)) (hp (src e)).w h ≫ (b e).left =
        (a e).left ≫ ModelMorphisms.Constructions.Foundations.genericModelLift (X₀ (dst e)) (p (dst e)) (hp (dst e)).w h := by
  classical
  let : Fintype E := Fintype.ofFinite E
  choose t ht b hb using fun e ↦ ModelMorphisms.Constructions.Foundations.morphism_between_models_descends
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

end OAI.ArithmeticGeometry.Models.CommonStage.Constructions.Foundations
