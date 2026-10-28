import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitHomExt

/-! # Group Hom Ext -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupHomExt.CM

noncomputable section

/-! For finite commutative group schemes over an algebraically closed
field, the actual neutral kernel and rational points detect morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupRetraction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition.CM

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (A B : Grp (Over (Spec (.of k)))) [IsFinite A.X.hom] [IsCommMonObj A.X]

theorem hom_ext (f g : A ⟶ B)
    (hn : Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (GroupRetraction.CM.componentMap A) ≫ f.hom.hom =
      Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (GroupRetraction.CM.componentMap A) ≫ g.hom.hom)
    (hp : ∀ p : Over.mk (𝟙 (Spec (.of k))) ⟶ A.X, p ≫ f.hom.hom = p ≫ g.hom.hom) :
    f = g := by
  let s := ConstantGroupMap.CM.groupMap (Spec (.of k))
    (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) A (MonoidHom.id _)
  have hs : s.hom.hom ≫ GroupRetraction.CM.componentMap A = 𝟙 _ :=
    congrArg (fun h : GroupDecomposition.CM.pointGroup A ⟶ GroupDecomposition.CM.pointGroup A => h.hom.hom) (GroupRetraction.CM.inclusion_retraction A)
  have he : s.hom.hom ≫ f.hom.hom = s.hom.hom ≫ g.hom.hom := by
    apply ConstantPointMap.CM.hom_ext
    intro p
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ f.hom.hom)
        (ConstantGroupMap.CM.groupMap_points (Spec (.of k))
          (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) A (MonoidHom.id _) p)).trans
        ((hp p).trans
          ((congrArg (· ≫ g.hom.hom)
            (ConstantGroupMap.CM.groupMap_points (Spec (.of k))
              (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) A (MonoidHom.id _) p).symm).trans
                (Category.assoc _ _ _))))
  apply Grp.hom_ext
  exact SplitHomExt.CM.hom_ext (GroupRetraction.CM.componentMap A) s.hom.hom hs f.hom.hom g.hom.hom hn he

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupHomExt.CM
