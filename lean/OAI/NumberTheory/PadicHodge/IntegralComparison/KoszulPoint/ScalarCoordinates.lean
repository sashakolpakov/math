import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SupportedIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SectionCoefficient

/-! # Scalar Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.ScalarCoordinates

noncomputable section

/-! Every original supported point class is the explicit duplicate
lift of the ordered wedge functional with its canonical base scalar. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
  (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  (hP : Function.Bijective (algebraMap R (P.obj (op (⊤_ C)))))
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  {L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (e : HomotopyEquiv L (KoszulPartial.Components.coefficient R P (Fin.append s t)))
  (d : ℕ) (hL : ∀ q, q ≠ d → L.ExactAt q)
  (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q,
    IsZero ((((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) d).obj (L.homology d)).X p).obj
      (op ((AugmentedOrdered.Cech.formal U q).obj a))))
  (e₀ : (R ⧸ Koszul.OrientedTopCohomology.ideal R (Fin.append s t)) ≃ₐ[k] k)

local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SupportedIso.iso R P hP U s t e d hL hzero (c+m)

def scalar (y : ((AugmentedOrdered.CechFunctor.bicomplex U L).total (.up ℕ)).homology (c+m)) : k :=
  Koszul.SectionCoefficient.coefficient k R (Fin.append s t) e₀ ((E).inv y)

def representative (y : ((AugmentedOrdered.CechFunctor.bicomplex U L).total (.up ℕ)).homology (c+m)) :=
  Koszul.SectionCoefficient.representative k R (Fin.append s t) e₀ ((E).inv y)

theorem evaluation (y : ((AugmentedOrdered.CechFunctor.bicomplex U L).total (.up ℕ)).homology (c+m)) :
    Koszul.OrientedTopCohomology.evaluation R (Fin.append s t)
      (representative k R P hP U s t e d hL hzero e₀ y) =
        algebraMap k R (scalar k R P hP U s t e d hL hzero e₀ y) :=
  Koszul.SectionCoefficient.representative_evaluation k R (Fin.append s t) e₀ ((E).inv y)

theorem lift_representative (y : ((AugmentedOrdered.CechFunctor.bicomplex U L).total (.up ℕ)).homology (c+m)) :
    homologyMap (SupportedTransfer.lift R P U s t ht e) (c+m)
      (TopHomologyCokernel.cycleClass
        (Koszul.OrientedTopCohomology.dualComplex R (Fin.append s t)) (c+m)
        (Koszul.OrientedTopCohomology.outgoing_isZero R (Fin.append s t))
        (representative k R P hP U s t e d hL hzero e₀ y)) = y := by
  rw [representative, Koszul.SectionCoefficient.cycle_representative]
  exact ConcreteCategory.congr_hom
    (SupportedIso.inverse_lift R P hP U s t ht e d hL hzero (c+m)) y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.ScalarCoordinates
