import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.OverlapPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant

/-! # Affine Overlap -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineOverlap

noncomputable section

/-!
# Ordinary scheme descent uses exactly the tensor-overlap gluing
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.OverlapPullback

/-- Equal test maps give the same transported ordinary descent isomorphism. -/
theorem overlapIso_heq {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    {base base' : Z ⟶ Y} {p q p' q' : Z ⟶ X}
    (hp : p ≫ f = base) (hq : q ≫ f = base) (hp' : p' ≫ f = base') (hq' : q' ≫ f = base')
    (hb : base = base') (heP : p = p') (heQ : q = q') :
    HEq (OverlapPullback.overlapIso f D base p q hp hq) (OverlapPullback.overlapIso f D base' p' q' hp' hq') := by
  cases hb
  cases heP
  cases heQ
  rfl

end

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCanonicalCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCoordinates
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapGluing

variable {R S : CommRingCat.{u}} (f : R ⟶ S)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => Spec.map f))

/-- The ordinary gluing on the actual kernel pair pulls back to the original affine tensor gluing. -/
def IsTensorGluing : Prop :=
  letI := f.hom.toAlgebra
  HEq (Geometric.OverlapGluing.extendedGluing (pullback.fst (Spec.map f) (Spec.map f))
    (pullback.snd (Spec.map f) (Spec.map f)) (Affine.CechPullback.overlapIso f).inv
    (D.obj PUnit.unit) (Geometric.CechInvariant.relationGluing (Spec.map f) D))
    (AffineDescent.overlapIso R S D)

theorem tensor_gluing : IsTensorGluing f D := by
  let := f.hom.toAlgebra
  let p := pullback.fst (Spec.map f) (Spec.map f)
  let q := pullback.snd (Spec.map f) (Spec.map f)
  let r := (Affine.CechPullback.overlapIso f).inv
  have hbase : r ≫ (q ≫ Spec.map f) = Affine.CechCoordinates.specMap (Affine.CechCoordinates.overlapBase R S) :=
    (Category.assoc r q (Spec.map f)).symm.trans
      ((congrArg (fun z => z ≫ Spec.map f) (Affine.CechPullback.overlapIso_inv_snd f)).trans
        (Affine.CechCoordinates.second_to_base R S))
  have he := OverlapPullback.overlapIso_pullback (Spec.map f) D
    (q ≫ Spec.map f) p q pullback.condition rfl r
  have ht := overlapIso_heq (Spec.map f) D
    ((Category.assoc r p (Spec.map f)).trans (congrArg (fun z => r ≫ z) pullback.condition))
    (Category.assoc r q (Spec.map f)) (Affine.CechCoordinates.first_to_base R S) (Affine.CechCoordinates.second_to_base R S)
    hbase (Affine.CechPullback.overlapIso_inv_fst f) (Affine.CechPullback.overlapIso_inv_snd f)
  exact (heq_of_eq he).trans ht

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineOverlap
