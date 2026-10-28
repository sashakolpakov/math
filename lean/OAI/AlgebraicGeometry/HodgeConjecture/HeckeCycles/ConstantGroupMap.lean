import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantMapMultiplication
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantPointEmbedding

/-! # Constant Group Map -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantGroupMap.CM

noncomputable section

/-! Promote the constructed constant-label map to a genuine group-scheme
morphism using its proved multiplication law on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantGroupPoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantMapMultiplication.CM

universe u
variable (S : Scheme.{u}) (G : Type u) [Group G] (A : Grp (Over S))
  (p : G →* (Over.mk (𝟙 S) ⟶ A.X))

instance schemeMap_isMonHom : IsMonHom (ConstantGroupPoints.CM.schemeMap S G A.X p) where
  one_hom := by
    rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact ConstantMapMultiplication.CM.preserves_one S G A.X p (𝟙_ (Over S))
  mul_hom := by
    rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
    exact ConstantMapMultiplication.CM.preserves_mul S G A.X p
      ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X ⊗ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X)
      (fst _ _) (snd _ _)

def groupMap : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G ⟶ A :=
  Grp.ofHom (A := (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) (B := A.X) (ConstantGroupPoints.CM.schemeMap S G A.X p)

theorem groupMap_points (g : G) :
    ConstantPointMap.CM.point S G g ≫ (groupMap S G A p).hom.hom = p g :=
  ConstantPointMap.CM.point_ofPoints S G A.X p g

theorem groupMap_points_bijective [PreconnectedSpace S] (s : S)
    (hp : Function.Bijective p) :
    Function.Bijective (fun x : Over.mk (𝟙 S) ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X =>
      x ≫ (groupMap S G A p).hom.hom) :=
  ConstantGroupPoints.CM.schemeMap_points_bijective S G A.X s p hp

theorem groupMap_closed {k : Type u} [Field k] (J : Type u) [Group J] [Finite J]
    (B : Grp (Over (Spec (.of k)))) [IsSeparated B.X.hom]
    (a : J →* (Over.mk (𝟙 (Spec (.of k))) ⟶ B.X)) (ha : Function.Injective a) :
    IsClosedImmersion (groupMap (Spec (.of k)) J B a).hom.hom.left :=
  ConstantPointEmbedding.CM.map_closed k J B.X a ha

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantGroupMap.CM
