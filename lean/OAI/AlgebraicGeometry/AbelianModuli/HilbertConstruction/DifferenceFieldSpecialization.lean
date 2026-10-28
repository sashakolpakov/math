import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferencePointBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.BaseChange
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceClassBaseChange

/-! # Difference Field Specialization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferenceFieldSpecialization

noncomputable section

/-! A field-valued parameter gives the actual Cartesian fiber of the
original difference family. Its line class is the difference-point
bundle on the changed abelian scheme, in every characteristic. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceClassBaseChange.Geometric

section Maps
variable {S : Scheme.{0}} {K : Type} [Field K] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (c : Spec (.of K) ⟶ S)
    (x : (Over.map c).obj (𝟙_ (Over (Spec (.of K)))) ⟶ A.scheme)

def differenceFieldSpecializationPoint :
    𝟙_ (Over (Spec (.of K))) ⟶ (A.pullback c).scheme :=
  (A.baseChangePointsEquiv c (𝟙_ (Over (Spec (.of K))))).symm x

def differenceFieldSpecializationMap :
    (A.pullback c).scheme.left ⟶ (A.scheme ⊗ A.scheme).left :=
  (lift ((Over.map c).map (toUnit (A.pullback c).scheme) ≫ x)
    (Dual.Data.DualAbelianData.baseChangeProjection A c)).left

theorem differenceFieldSpecializationMap_fst :
    differenceFieldSpecializationMap A c x ≫ pullback.fst A.scheme.hom A.scheme.hom =
      (A.pullback c).scheme.hom ≫ x.left :=
  congrArg Over.Hom.left (lift_fst
    ((Over.map c).map (toUnit (A.pullback c).scheme) ≫ x) (Dual.Data.DualAbelianData.baseChangeProjection A c))

theorem differenceFieldSpecializationMap_snd :
    differenceFieldSpecializationMap A c x ≫ pullback.snd A.scheme.hom A.scheme.hom =
      pullback.fst A.scheme.hom c := by
  have h := congrArg Over.Hom.left (lift_snd
    ((Over.map c).map (toUnit (A.pullback c).scheme) ≫ x) (Dual.Data.DualAbelianData.baseChangeProjection A c))
  change differenceFieldSpecializationMap A c x ≫ pullback.snd A.scheme.hom A.scheme.hom =
    (𝟙 (A.pullback c).scheme.left) ≫ pullback.fst A.scheme.hom c at h
  exact h.trans (Category.id_comp _)

theorem differenceFieldSpecialization_isPullback :
    IsPullback (differenceFieldSpecializationMap A c x) (A.pullback c).scheme.hom
      (pullback.fst A.scheme.hom A.scheme.hom) x.left := by
  have hx : x.left ≫ A.scheme.hom = c := x.w.trans (Category.id_comp c)
  have hr : IsPullback
      (differenceFieldSpecializationMap A c x ≫ pullback.snd A.scheme.hom A.scheme.hom)
      (A.pullback c).scheme.hom A.scheme.hom (x.left ≫ A.scheme.hom) := by
    rw [differenceFieldSpecializationMap_snd, hx]
    exact IsPullback.of_hasPullback A.scheme.hom c
  exact IsPullback.of_right hr (differenceFieldSpecializationMap_fst A c x)
    (IsPullback.of_hasPullback A.scheme.hom A.scheme.hom).flip

end Maps

private theorem differenceClass_baseChangePoints
    {S S' : Scheme.{0}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
    (q : Line.Bundles.LineBundle.IsoClass A.scheme.left) (c : S' ⟶ S) (T : Over S')
    (a b : T ⟶ (A.pullback c).scheme) :
    RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme q
        (A.baseChangePointsEquiv c T a) (A.baseChangePointsEquiv c T b) =
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass (A.pullback c).scheme
        (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst A.scheme.hom c) q) a b := by
  have hp (u : T ⟶ (A.pullback c).scheme) :
      RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.baseChangePointsEquiv c T u).left q =
        RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback u.left (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst A.scheme.hom c) q) :=
    (congrArg (fun f => RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback f q)
      (A.baseChangePointsEquiv_apply c T u)).trans
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp u.left (pullback.fst A.scheme.hom c) q).symm
  have hm : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback
      (A.baseChangePointsEquiv c T a * A.baseChangePointsEquiv c T b).left q =
        RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (a * b).left (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst A.scheme.hom c) q) :=
    (congrArg (fun u : (Over.map c).obj T ⟶ A.scheme => RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback u.left q)
      ((A.baseChangePointsMulEquiv c T).map_mul a b).symm).trans (hp (a * b))
  exact congrArg₂ Line.Bundles.LineBundle.tensorClass
    (congrArg₂ Line.Bundles.LineBundle.tensorClass hm (congrArg Picard.Homomorphisms.LineBundleDual.Construction.dualLineBundleClass (hp a)))
    (congrArg Picard.Homomorphisms.LineBundleDual.Construction.dualLineBundleClass (hp b))

private theorem relativeDifference_pair_baseChangeField
    {k K : Type} [Field k] [Field K] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of k))) (L : Line.Bundles.LineBundle A.scheme.left)
    (c : Spec (.of K) ⟶ Spec (.of k)) (T : Over (Spec (.of K)))
    (a b : T ⟶ (A.pullback c).scheme) :
    Line.Bundles.LineBundle.classOf ((Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).pullback
        (lift (A.baseChangePointsEquiv c T a) (A.baseChangePointsEquiv c T b)).left) =
      Line.Bundles.LineBundle.classOf ((Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle (A.pullback c)
        (L.pullback (pullback.fst A.scheme.hom c))).pullback (lift a b).left) := by
  rw [Picard.ThetaConstruction.DifferenceClassBaseChange.Geometric.relativeDifference_pair_class, Picard.ThetaConstruction.DifferenceClassBaseChange.Geometric.relativeDifference_pair_class,
    Picard.ThetaConstruction.DifferenceClassBaseChange.Geometric.identityNormalizedLine_class_overField, Picard.ThetaConstruction.DifferenceClassBaseChange.Geometric.identityNormalizedLine_class_overField]
  exact differenceClass_baseChangePoints A (Line.Bundles.LineBundle.classOf L) c T a b

theorem differenceFieldSpecialization_class
    {k K : Type} [Field k] [Field K] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of k))) (L : Line.Bundles.LineBundle A.scheme.left)
    (c : Spec (.of K) ⟶ Spec (.of k))
    (x : (Over.map c).obj (𝟙_ (Over (Spec (.of K)))) ⟶ A.scheme) :
    Line.Bundles.LineBundle.classOf ((Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).pullback
        (differenceFieldSpecializationMap A c x)) =
      Line.Bundles.LineBundle.classOf (DifferencePointBundles.differencePointBundle (A.pullback c)
        (L.pullback (pullback.fst A.scheme.hom c)) (differenceFieldSpecializationPoint A c x)) := by
  let B := (A.pullback c).scheme
  let a := differenceFieldSpecializationPoint A c x
  have ha : A.baseChangePointsEquiv c (𝟙_ (Over (Spec (.of K)))) a = x :=
    (A.baseChangePointsEquiv c (𝟙_ (Over (Spec (.of K))))).apply_symm_apply x
  have hfirst : A.baseChangePointsEquiv c B (toUnit B ≫ a) =
      (Over.map c).map (toUnit B) ≫ x := by
    rw [Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_precomp, ha]
  have h := relativeDifference_pair_baseChangeField A L c B (toUnit B ≫ a) (𝟙 B)
  rw [hfirst] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferenceFieldSpecialization
