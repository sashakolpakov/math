import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.TotalResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForget

/-! # Forget -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Forget

noncomputable section

/-! The supported mixed map forgets to the actual dual normal-Koszul
inclusion. This records the augmentation normalization needed for the
section quotient, in every cochain degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForget OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C)
  (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

def ambientMap : Components.source R s t ⟶ AugmentedOrdered.CechForget.ambientComplex (Components.coefficient R P s) :=
  Total.map R P U s t ht ≫ AugmentedOrdered.CechForget.forgetSupport U (Components.coefficient R P s)

theorem ambientMap_apply (n : ℕ)
    (φ : Module.Dual R (⋀[R]^n (Fractions.ambient R (c := c) (m := m))))
    (x : ⋀[R]^n (Fractions.normal R (c := c))) :
    (show (⋀[R]^n (Fractions.normal R (c := c))) →ₗ[R] P.obj (op (⊤_ C)) from
      (ambientMap R P U s t ht).f n φ) x =
      algebraMap R (P.obj (op (⊤_ C)))
        (φ (exteriorPower.map n (LinearMap.inl R (Fractions.normal R (c := c)) (Fractions.parameters R (m := m))) x)) := by
  have hm := TotalResidue.map_coordinate R P U s t ht n n 0 (by omega) AugmentedOrdered.CechZero.emptyIndex
  have he := ConcreteCategory.congr_hom hm φ
  let z : ((Components.coefficient R P s).X n).obj (op ((AugmentedOrdered.Cech.formal U 0).obj AugmentedOrdered.CechZero.emptyIndex)) :=
    (Pi.π (fun a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) 0 =>
      ((Components.coefficient R P s).X n).obj (op ((AugmentedOrdered.Cech.formal U 0).obj a))) AugmentedOrdered.CechZero.emptyIndex)
      ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (target R P U s)) n 0 n
        ((Total.map R P U s t ht).f n φ))
  change (P.map (AugmentedOrdered.CechZero.emptyProductMap U AugmentedOrdered.CechZero.emptyIndex).op).hom
    ((show (⋀[R]^n (Fractions.normal R (c := c))) →ₗ[R] P.obj (op ((AugmentedOrdered.Cech.formal U 0).obj AugmentedOrdered.CechZero.emptyIndex)) from z) x) = _
  have hcoord := congrArg (fun z : ((Components.coefficient R P s).X n).obj (op ((AugmentedOrdered.Cech.formal U 0).obj AugmentedOrdered.CechZero.emptyIndex)) =>
    (show (⋀[R]^n (Fractions.normal R (c := c))) →ₗ[R] P.obj (op ((AugmentedOrdered.Cech.formal U 0).obj AugmentedOrdered.CechZero.emptyIndex)) from z) x) he
  have hz := Fractions.coordinate_zero R P U t ht n AugmentedOrdered.CechZero.emptyIndex φ x
  exact (congrArg (P.map (AugmentedOrdered.CechZero.emptyProductMap U AugmentedOrdered.CechZero.emptyIndex).op).hom
    (hcoord.trans hz)).trans ((P.map (AugmentedOrdered.CechZero.emptyProductMap U AugmentedOrdered.CechZero.emptyIndex).op).hom.commutes _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Forget
