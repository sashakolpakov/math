import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantPointMap
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups

/-! # Constant Group Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantGroupPoints.CM

noncomputable section

/-! The labels of the actual constant group scheme are its base-valued
points over a connected base. Maps built from geometric torsion points
therefore have precisely the prescribed map on those points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction

universe u
variable (S : Scheme.{u}) (G : Type u) [Group G]

def labelsToPoints : G →* (Over.mk (𝟙 S) ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) :=
  (((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G).app (.op (Over.mk (𝟙 S)))).groupIsoToMulEquiv.symm.toMonoidHom).comp
    LocallyConstant.constMonoidHom

theorem labelsToPoints_apply (g : G) :
    labelsToPoints S G g = ConstantPointMap.CM.point S G g := by
  apply ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G).app (.op (Over.mk (𝟙 S)))).groupIsoToMulEquiv.injective
  change ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G).app (.op (Over.mk (𝟙 S)))).groupIsoToMulEquiv
    (((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G).app (.op (Over.mk (𝟙 S)))).groupIsoToMulEquiv.symm
      (LocallyConstant.const S g)) = _
  refine (((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G).app (.op (Over.mk (𝟙 S)))).groupIsoToMulEquiv.apply_symm_apply
    (LocallyConstant.const S g)).trans ?_
  change LocallyConstant.const S g =
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint (Over.mk (𝟙 S)) (ConstantPointMap.CM.point S G g)
  apply LocallyConstant.ext
  intro x
  exact (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι g x).symm

def constantEquiv [PreconnectedSpace S] (s : S) : G ≃* LocallyConstant S G where
  toFun := LocallyConstant.const S
  invFun f := f s
  left_inv _ := rfl
  right_inv f := (f.eq_const s).symm
  map_mul' _ _ := rfl

def pointsEquiv [PreconnectedSpace S] (s : S) :
    G ≃* (Over.mk (𝟙 S) ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) :=
  (constantEquiv S G s).trans
    ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G).app (.op (Over.mk (𝟙 S)))).groupIsoToMulEquiv.symm

theorem pointsEquiv_apply [PreconnectedSpace S] (s : S) (g : G) :
    pointsEquiv S G s g = ConstantPointMap.CM.point S G g :=
  labelsToPoints_apply S G g

variable (A : Over S) [GrpObj A]

def schemeMap (p : G →* (Over.mk (𝟙 S) ⟶ A)) : (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X ⟶ A :=
  ConstantPointMap.CM.ofPoints S G A p

theorem schemeMap_points [PreconnectedSpace S] (s : S)
    (p : G →* (Over.mk (𝟙 S) ⟶ A)) (g : G) :
    pointsEquiv S G s g ≫ schemeMap S G A p = p g := by
  rw [pointsEquiv_apply]
  exact ConstantPointMap.CM.point_ofPoints S G A p g

theorem schemeMap_points_bijective [PreconnectedSpace S] (s : S)
    (p : G →* (Over.mk (𝟙 S) ⟶ A)) (hp : Function.Bijective p) :
    Function.Bijective (fun x : Over.mk (𝟙 S) ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X =>
      x ≫ schemeMap S G A p) := by
  have heq : (fun x : Over.mk (𝟙 S) ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X =>
      x ≫ schemeMap S G A p) = fun x => p ((pointsEquiv S G s).symm x) := by
    funext x
    obtain ⟨g, rfl⟩ := (pointsEquiv S G s).surjective x
    rw [MulEquiv.symm_apply_apply]
    exact schemeMap_points S G A s p g
  rw [heq]
  exact hp.comp (pointsEquiv S G s).symm.bijective

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantGroupPoints.CM
