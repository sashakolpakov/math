import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.ParameterQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilinearLength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EveryStalkOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationEuler

/-! # Principal Base Change -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalBaseChange

noncomputable section

section

/-! The generic length of a principal quotient of an affine prime
module is the actual divisor order on its native reduced support. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace SupportOrder

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

variable (R : Type) [CommRing R] (q p : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal)

def baseEquiv :
    letI : Algebra R ((Spec (.of R)).presheaf.stalk p) := (StructureSheaf.toStalk R p).hom.toAlgebra
    (Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk p)).obj (.of R (R ⧸ q.asIdeal)) ≃ₗ[
      (Spec (.of R)).presheaf.stalk p] CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) (SupportStalk.support R q) p (SupportStalk.mem R q p hqp) := by
  let : Algebra R ((Spec (.of R)).presheaf.stalk p) := (StructureSheaf.toStalk R p).hom.toAlgebra
  exact (Ideal.qoutMapEquivTensorQout (R := R) (I := q.asIdeal)
    ((Spec (.of R)).presheaf.stalk p)).symm.trans (SupportStalk.moduleEquiv R q p hqp).symm

theorem length (r : R) :
    FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal)
      (.of R (QuotSMulTop r (R ⧸ q.asIdeal))) =
    Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportStalk.support R q)).presheaf.stalk
      (CycleClass.Thom.IntersectionGeometry.supportPreimage (SupportStalk.support R q) p (SupportStalk.mem R q p hqp)))
        (Local.Principal.supportStalkMap (Spec (.of R)) (SupportStalk.support R q) p (SupportStalk.mem R q p hqp)
          (StructureSheaf.toStalk R p r)) := by
  let S := (Spec (.of R)).presheaf.stalk p
  let T := (CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportStalk.support R q)).presheaf.stalk
    (CycleClass.Thom.IntersectionGeometry.supportPreimage (SupportStalk.support R q) p (SupportStalk.mem R q p hqp))
  let : Algebra R S := (StructureSheaf.toStalk R p).hom.toAlgebra
  let : Algebra S T := (Local.Principal.supportStalkMap (Spec (.of R)) (SupportStalk.support R q) p (SupportStalk.mem R q p hqp)).hom.toAlgebra
  rw [SemilinearLength.baseChange_length R (Localization.AtPrime p.asIdeal) S
    (StructureSheaf.stalkIso R p)]
  exact (Flat.ParameterQuotient.length R S (.of R (R ⧸ q.asIdeal)) r
    (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) (SupportStalk.support R q) p (SupportStalk.mem R q p hqp))
    (baseEquiv R q p hqp)).trans
      (Principal.Order.quotient_length S T
        (Local.Principal.supportStalkMap_surjective (Spec (.of R)) (SupportStalk.support R q) p (SupportStalk.mem R q p hqp))
        (StructureSheaf.toStalk R p r))

theorem image_ne_zero (r : R) (hr : r ∉ q.asIdeal) :
    Local.Principal.supportStalkMap (Spec (.of R)) (SupportStalk.support R q) p (SupportStalk.mem R q p hqp)
      (StructureSheaf.toStalk R p r) ≠ 0 := by
  intro h
  apply hr
  rw [← SupportStalk.kernel_comap R q p hqp]
  exact h

theorem order [IsNoetherianRing R] (r : R) (hr : r ∉ q.asIdeal) :
    let W := SupportStalk.support R q
    let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W p (SupportStalk.mem R q p hqp)
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).ord
      (algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y)
        (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField
        (Local.Principal.supportStalkMap (Spec (.of R)) W p (SupportStalk.mem R q p hqp) (StructureSheaf.toStalk R p r))) y =
      ((FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal)
        (.of R (QuotSMulTop r (R ⧸ q.asIdeal))))).toNat := by
  rw [length R q p hqp r]
  exact EveryStalkOrder.order _ _ _ (image_ne_zero R q p hqp r hr)

end SupportOrder

end

/-! Localization of an affine principal quotient is the actual
principal quotient of the native reduced-support stalk module. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk

variable (R : Type) [CommRing R] (q x : PrimeSpectrum R) (hqx : q.asIdeal ≤ x.asIdeal) (r : R)

def equiv :
    letI : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
    (Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj
      (.of R (QuotSMulTop r (R ⧸ q.asIdeal))) ≃ₗ[(Spec (.of R)).presheaf.stalk x]
        QuotSMulTop (StructureSheaf.toStalk R x r)
          (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) (SupportStalk.support R q) x (SupportStalk.mem R q x hqx)) := by
  let S := (Spec (.of R)).presheaf.stalk x
  let : Algebra R S := (StructureSheaf.toStalk R x).hom.toAlgebra
  exact (Flat.ParameterQuotient.iso R S (.of R (R ⧸ q.asIdeal)) r).toLinearEquiv.trans
    (QuotSMulTop.congr (StructureSheaf.toStalk R x r)
      (SupportOrder.baseEquiv R q x hqx))

theorem euler (N : ModuleCat ((Spec (.of R)).presheaf.stalk x)) (d : ℕ) :
    letI : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
    Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
      ((Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj
        (.of R (QuotSMulTop r (R ⧸ q.asIdeal)))) N d =
      Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
        (.of _ (QuotSMulTop (StructureSheaf.toStalk R x r)
          (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) (SupportStalk.support R q) x (SupportStalk.mem R q x hqx)))) N d := by
  let : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
  exact PrimeFiltrationEuler.euler_iso_left _ (equiv R q x hqx r).toModuleIso N d

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalBaseChange
