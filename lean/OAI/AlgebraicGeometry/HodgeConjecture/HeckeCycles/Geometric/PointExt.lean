import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricExt
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Point Ext -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM

noncomputable section

/-! Actual morphisms are detected on the closed points of a dense open
subscheme. This is the geometric input for detection on ordinary points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k : Type} [Field k] [IsAlgClosed k]

abbrev pointBase (k : Type) [Field k] : Over (Spec (.of k)) := Over.mk (𝟙 _)

theorem over_hom_ext_on_dense_open
    {X Y : Over (Spec (.of k))} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (f g : X ⟶ Y) (U : X.left.Opens) (hU : Dense (U : Set X.left))
    (h : ∀ p : pointBase k ⟶ X,
      p.left (IsLocalRing.closedPoint k) ∈ U → p ≫ f = p ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  apply ext_of_apply_eq Y.hom U U.isOpen.isLocallyClosed hU
  · intro x hx hclosed
    obtain ⟨⟨p, hp⟩, he⟩ := (pointEquivClosedPoint X.hom).surjective ⟨x, hclosed⟩
    have hpx : p (IsLocalRing.closedPoint k) = x := congrArg Subtype.val he
    let a : pointBase k ⟶ X := Over.homMk p hp
    have ha : a.left (IsLocalRing.closedPoint k) ∈ U := by
      change p (IsLocalRing.closedPoint k) ∈ U
      rwa [hpx]
    have hh := congrArg (fun z : pointBase k ⟶ Y => z.left (IsLocalRing.closedPoint k))
      (h a ha)
    change f.left (p (IsLocalRing.closedPoint k)) =
      g.left (p (IsLocalRing.closedPoint k)) at hh
    rwa [hpx] at hh
  · exact f.w.trans g.w.symm

theorem over_hom_ext_on_points
    {X Y : Over (Spec (.of k))} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (f g : X ⟶ Y) (h : ∀ p : pointBase k ⟶ X, p ≫ f = p ≫ g) : f = g :=
  over_hom_ext_on_dense_open f g ⊤ dense_univ (fun p _ => h p)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM
