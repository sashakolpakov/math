import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientResidueClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.FractionQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechSingleTopCoordinates
import Mathlib.Data.Int.Order.Units

/-! # Fraction Ordinary Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.FractionOrdinaryQuotient.Ordinary

noncomputable section

/-! The ordinary full-intersection fraction depends only on its
numerator modulo the point ideal. The proof passes through the original
Koszul residue and retains its signed single-total coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  (N : Cᵒᵖ ⥤ ModuleCat.{u} R) (α : KoszulPartial.Fractions.modules R P ⟶ N)
  (hN : ∀ (v : Cᵒᵖ) (i : Fin c) (x : N.obj v), s i • x = 0)

private theorem cardinal : Fintype.card (ULift.{u} (Fin m)) = m := by simp

abbrev numerator := α.app (op (AugmentedOrdered.CechCoordinates.topObject U m (cardinal (m := m))))
  (KoszulPartial.Fractions.reciprocal R P U t ht (AugmentedOrdered.CechCoordinates.topIndex m (cardinal (m := m))))

abbrev fractionClass := AugmentedOrdered.CechTopClass.topClass U N m (cardinal (m := m)) (numerator R P U t ht N α)

def comparisonMap : ((AugmentedOrdered.CechFunctor.bicomplex U (KoszulPartial.Components.coefficient R P s)).total (.up ℕ)).homology (c+m) ⟶
    (AugmentedOrdered.Cech.complex U N).homology m :=
  homologyMap (AugmentedOrdered.CechTopNaturality.totalMap U (CoefficientResidue.complexMap R P s N α hN)) (c+m) ≫
    eqToHom (congrArg (fun j =>
      ((AugmentedOrdered.CechFunctor.bicomplex U (CoefficientResidueClass.residueTarget R (c := c) N)).total
        (.up ℕ)).homology j) (Nat.add_comm c m)) ≫
      (Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor U) N c m).hom

theorem residueValue :
    CoefficientResidueClass.residueValue R P U t ht N α
      (KoszulPartial.TopResidue.functional R (c := c) (m := m)) =
    AugmentedOrdered.CechSingleTopCoordinates.singleValue U N m (cardinal (m := m)) c
      (numerator R P U t ht N α) := by
  simp only [CoefficientResidueClass.residueValue,
    KoszulPartial.TopResidue.functional, TopExteriorCoordinates.coordinate_generator,
    map_one, mul_one, AugmentedOrdered.CechSingleTopCoordinates.singleValue, numerator]

include hN in
theorem comparison_class :
    comparisonMap R P U s N α hN
      (KoszulPartial.PartialClass.supportedClass R P U s t ht
        (KoszulPartial.TopResidue.functional R)) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c m • fractionClass R P U t ht N α := by
  change (Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor U) N c m).hom
    ((eqToHom (congrArg (fun j =>
      ((AugmentedOrdered.CechFunctor.bicomplex U (CoefficientResidueClass.residueTarget R (c := c) N)).total
        (.up ℕ)).homology j) (Nat.add_comm c m)))
      (homologyMap (AugmentedOrdered.CechTopNaturality.totalMap U (CoefficientResidue.complexMap R P s N α hN)) (c+m)
        (KoszulPartial.PartialClass.supportedClass R P U s t ht
          (KoszulPartial.TopResidue.functional R)))) = _
  rw [CoefficientResidueClass.supportedClass_residue R P U s t ht N α hN]
  have hv := residueValue R P U t ht N α (c := c)
  rw [hv]
  exact AugmentedOrdered.CechSingleTopCoordinates.topTotalClass_coordinates U N m
    (cardinal (m := m)) c (numerator R P U t ht N α) _

include hN in
theorem weighted_eq (a b : R)
    (h : Ideal.Quotient.mk (OrientedTopCohomology.ideal R (Fin.append s t)) a =
      Ideal.Quotient.mk (OrientedTopCohomology.ideal R (Fin.append s t)) b) :
    a • fractionClass R P U t ht N α = b • fractionClass R P U t ht N α := by
  have h' := congrArg (comparisonMap R P U s N α hN)
    (FractionQuotient.weighted_eq R s t P U ht a b h)
  simp only [map_smul, comparison_class] at h'
  rw [smul_comm a, smul_comm b] at h'
  have h'' := congrArg (fun x => ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c m • x) h'
  simpa only [smul_smul, Int.units_mul_self, one_smul] using h''

include hN in
theorem weighted_of_kernel {k : Type u} [CommRing k] (η : R →+* k)
    (hk : OrientedTopCohomology.ideal R (Fin.append s t) = RingHom.ker η)
    (z : R) (hz : η z=1) (a : R) :
    (z*a) • fractionClass R P U t ht N α = a • fractionClass R P U t ht N α := by
  apply weighted_eq R P U s t ht N α hN
  apply Ideal.Quotient.eq.mpr
  rw [hk]
  change η (z*a-a)=0
  rw [map_sub, map_mul, hz, one_mul, sub_self]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.FractionOrdinaryQuotient.Ordinary
