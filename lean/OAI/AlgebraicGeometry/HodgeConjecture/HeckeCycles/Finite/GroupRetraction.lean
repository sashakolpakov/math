import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PointRetraction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantGroupMap

/-! # Group Retraction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupRetraction.CM

noncomputable section

/-! The canonical map from a finite group scheme to its constant point
group preserves the group law. It splits the actual inclusion of all
rational points, rather than identifying a nonreduced group with them. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantGroupPoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PointRetraction.CM

universe u

local instance (S : Scheme.{u}) (G : Type u) [Group G] : GrpObj (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G) :=
  (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).grp

theorem point_mul (S : Scheme.{u}) (G : Type u) [Group G] (x y : G) :
    (ConstantPointMap.CM.point S G (x * y) : Over.mk (𝟙 S) ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) =
      (ConstantPointMap.CM.point S G x : Over.mk (𝟙 S) ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) *
        ConstantPointMap.CM.point S G y :=
  (ConstantGroupPoints.CM.labelsToPoints_apply S G (x * y)).symm.trans
    (((ConstantGroupPoints.CM.labelsToPoints S G).map_mul x y).trans
      (congrArg₂ (fun a b : Over.mk (𝟙 S) ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X => a * b)
        (ConstantGroupPoints.CM.labelsToPoints_apply S G x) (ConstantGroupPoints.CM.labelsToPoints_apply S G y)))

variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Grp (Over (Spec (.of k)))) [IsFinite A.X.hom]

def componentMap : A.X ⟶
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X)).X :=
  PointRetraction.CM.retraction A.X

theorem componentMap_one :
    (1 : Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) ≫ componentMap A = 1 :=
  (PointRetraction.CM.retraction_points A.X 1).trans
    ((ConstantGroupPoints.CM.labelsToPoints_apply (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) 1).symm.trans
      (ConstantGroupPoints.CM.labelsToPoints (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X)).map_one)

theorem componentMap_mul (x y : Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) :
    (x * y) ≫ componentMap A = (x ≫ componentMap A) * (y ≫ componentMap A) :=
  (PointRetraction.CM.retraction_points A.X (x * y)).trans
    ((point_mul (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) x y).trans
      (congrArg₂ (· * ·) (PointRetraction.CM.retraction_points A.X x).symm (PointRetraction.CM.retraction_points A.X y).symm))

instance componentMap_isMonHom : IsMonHom (componentMap A) where
  one_hom := by
    rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact componentMap_one A
  mul_hom := by
    have : IsFinite (A.X ⊗ A.X).hom := by
      change IsFinite (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
      infer_instance
    apply PointRetraction.CM.hom_ext_to_constant (A.X ⊗ A.X) (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X)
    intro p
    change @Eq (Over.mk (𝟙 (Spec (.of k))) ⟶
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X)).X)
      (p ≫ μ[A.X] ≫ componentMap A)
      (p ≫ (componentMap A ⊗ₘ componentMap A) ≫
        μ[(AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X)).X])
    rw [← Category.assoc, MonObj.mul_eq_mul, MonObj.comp_mul]
    rw [componentMap_mul]
    rw [MonObj.mul_eq_mul, MonObj.comp_mul, MonObj.comp_mul]
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd]

def groupRetraction : A ⟶ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k))
    (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) :=
  Grp.ofHom (A := A.X)
    (B := (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X)).X)
    (componentMap A)

theorem inclusion_retraction :
    ConstantGroupMap.CM.groupMap (Spec (.of k))
      (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) A (MonoidHom.id _) ≫ groupRetraction A = 𝟙 _ := by
  apply Grp.hom_ext
  exact PointRetraction.CM.section_retraction A.X

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupRetraction.CM
