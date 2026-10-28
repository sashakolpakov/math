import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupRetraction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitGroupScheme
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels

/-! # Group Decomposition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition.CM

noncomputable section

/-! A finite commutative group scheme over an algebraically closed field
splits as its point group and the kernel of the canonical point retraction.
The kernel has only its identity rational point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupRetraction.CM

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Grp (Over (Spec (.of k)))) [IsFinite A.X.hom] [IsCommMonObj A.X]

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

def pointGroup : Grp (Over (Spec (.of k))) :=
  AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X)

def neutralPart : Grp (Over (Spec (.of k))) := Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject (GroupRetraction.CM.componentMap A))

def decomposition : Grp.mk ((neutralPart A).X ⊗ (pointGroup A).X) ≅ A :=
  SplitGroupScheme.CM.productGroupIso (GroupRetraction.CM.componentMap A)
    (ConstantGroupMap.CM.groupMap (Spec (.of k))
      (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) A (MonoidHom.id _)).hom.hom
    (congrArg (fun f : pointGroup A ⟶ pointGroup A => f.hom.hom) (GroupRetraction.CM.inclusion_retraction A))

theorem neutral_points_trivial (p : Over.mk (𝟙 (Spec (.of k))) ⟶ (neutralPart A).X) : p = 1 := by
  apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (GroupRetraction.CM.componentMap A))).mp
  refine Eq.trans ?_ (MonObj.one_comp (X := Over.mk (𝟙 (Spec (.of k))))
    (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (GroupRetraction.CM.componentMap A))).symm
  let x := p ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (GroupRetraction.CM.componentMap A)
  have hx : x ≫ GroupRetraction.CM.componentMap A = 1 :=
    (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv (GroupRetraction.CM.componentMap A) (Over.mk (𝟙 (Spec (.of k)))) p).property
  let e := ConstantGroupPoints.CM.pointsEquiv (Spec (.of k))
    (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) (IsLocalRing.closedPoint k)
  have he : e x = 1 :=
    (ConstantGroupPoints.CM.pointsEquiv_apply (Spec (.of k))
      (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) (IsLocalRing.closedPoint k) x).trans
      ((PointRetraction.CM.retraction_points A.X x).symm.trans hx)
  exact e.injective (he.trans (map_one e).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition.CM
