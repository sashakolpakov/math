import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Total
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.TopResidue

/-! # Total Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.TotalResidue

noncomputable section

/-! The genuine total chain map carries the ordered top functional to
the literal reciprocal point-parameter coefficient after normal evaluation. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C)
  (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

@[reassoc]
theorem map_coordinate (n p q : ℕ) (h : p + q = n) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q) :
    (Total.map R P U s t ht).f n ≫
      (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (target R P U s)) p q n ≫
        Pi.π (fun b : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q =>
          ((Components.coefficient R P s).X p).obj (op ((AugmentedOrdered.Cech.formal U q).obj b))) a =
    ModuleCat.ofHom (Components.coordinateAt R P U t ht n p q h a) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ Pi.π _ a) (Total.map_projection R P U s t ht n p q h)).trans
      (Components.component_projection R P U s t ht n p q h a))

theorem top (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m) :
    (show (⋀[R]^c (Fractions.normal R (c := c))) →ₗ[R] P.obj (op ((AugmentedOrdered.Cech.formal U m).obj a)) from
      (Pi.π (fun b : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m =>
      ((Components.coefficient R P s).X c).obj (op ((AugmentedOrdered.Cech.formal U m).obj b))) a)
      ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (target R P U s)) c m (c + m)
        ((Total.map R P U s t ht).f (c + m)
          (TopResidue.functional R (c := c) (m := m)))))
      (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c))) = Fractions.reciprocal R P U t ht a := by
  have h := ConcreteCategory.congr_hom (map_coordinate R P U s t ht (c + m) c m rfl a)
    (TopResidue.functional R (c := c) (m := m))
  have he := LinearMap.congr_fun h (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c)))
  exact he.trans (TopResidue.coordinate_top R P U t ht a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.TotalResidue
