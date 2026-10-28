import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.FractionOrdinaryQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.TopClassMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Fraction

/-! # Ordinary Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrdinaryFraction.Ordinary

noncomputable section

/-! Ordinary fractional section classes on a genuine principal open
cover depend only on the numerator modulo the parameter ideal. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) (ω : Γ(N,U))

def multiplication :
    KoszulPartial.Fractions.modules Γ(X,U) (SectionPresheaf.rings U hU) ⟶ SectionPresheaf.modules U hU N where
  app r := ModuleCat.ofHom
    { toFun x := (show Γ(X,SectionPresheaf.openSubset U r.unop) from x) •
          N.presheaf.map (SectionPresheaf.inclusion U r.unop).op ω
      map_add' x y := by
        change Γ(X,SectionPresheaf.openSubset U r.unop) at x y
        exact add_smul x y _
      map_smul' a x := by
        change Γ(X,SectionPresheaf.openSubset U r.unop) at x
        change (algebraMap Γ(X,U) Γ(X,SectionPresheaf.openSubset U r.unop) a * x) •
            N.presheaf.map (SectionPresheaf.inclusion U r.unop).op ω =
          algebraMap Γ(X,U) Γ(X,SectionPresheaf.openSubset U r.unop) a •
            (x • N.presheaf.map (SectionPresheaf.inclusion U r.unop).op ω)
        exact mul_smul _ _ _ }
  naturality {r s} a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Γ(X,SectionPresheaf.openSubset U r.unop) at x
    change (X.presheaf.map (SectionPresheaf.arrow U hU a.unop).op x) •
        N.presheaf.map (SectionPresheaf.inclusion U s.unop).op ω =
      N.presheaf.map (SectionPresheaf.arrow U hU a.unop).op (x • N.presheaf.map (SectionPresheaf.inclusion U r.unop).op ω)
    rw [N.map_smul]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← N.presheaf.map_comp]
    rfl

variable {m : ℕ} (t : Fin m → Γ(X,U))

private theorem cardinal : Fintype.card (ULift.{u} (Fin m))=m := by simp

abbrev reciprocal : Γ(X,SectionPresheaf.openSubset U (AugmentedOrdered.CechCoordinates.topObject (PrincipalPoint.Fraction.family U t) m
    (cardinal (m := m)))) :=
  KoszulPartial.Fractions.reciprocal Γ(X,U) (SectionPresheaf.rings U hU)
    (PrincipalPoint.Fraction.family U t) t (PrincipalPoint.Fraction.units U hU t)
    (AugmentedOrdered.CechCoordinates.topIndex m (cardinal (m := m)))

def value (a : Γ(X,U)) :=
  AugmentedOrdered.CechTopClass.topClass (PrincipalPoint.Fraction.family U t) (SectionPresheaf.modules U hU N) m (cardinal (m := m))
    ((multiplication U hU N ω).app
      (op (AugmentedOrdered.CechCoordinates.topObject (PrincipalPoint.Fraction.family U t) m (cardinal (m := m))))
      (reciprocal U hU t * algebraMap Γ(X,U) _ a))

theorem value_eq (a : Γ(X,U)) : value U hU N ω t a =
    a • Koszul.FractionOrdinaryQuotient.Ordinary.fractionClass Γ(X,U) (SectionPresheaf.rings U hU)
      (PrincipalPoint.Fraction.family U t) t (PrincipalPoint.Fraction.units U hU t)
      (SectionPresheaf.modules U hU N) (multiplication U hU N ω) := by
  let v := reciprocal U hU t
  let f := (multiplication U hU N ω).app
    (op (AugmentedOrdered.CechCoordinates.topObject (PrincipalPoint.Fraction.family U t) m (cardinal (m := m))))
  have hv : f (v * algebraMap Γ(X,U) _ a) = a • f v := by
    rw [mul_comm]
    exact f.hom.map_smul a v
  dsimp only [value, Koszul.FractionOrdinaryQuotient.Ordinary.fractionClass,
    Koszul.FractionOrdinaryQuotient.Ordinary.numerator]
  rw [hv]
  rw [← AugmentedCech.TopClassMap.module_apply,
    ← AugmentedCech.TopClassMap.module_apply]
  exact (AugmentedCech.TopClassMap.map (PrincipalPoint.Fraction.family U t)
    (SectionPresheaf.modules U hU N) m (cardinal (m := m))).hom.map_smul a (f v)

private theorem empty_parameters :
    Koszul.OrientedTopCohomology.ideal Γ(X,U)
      (Fin.append (Fin.elim0 : Fin 0 → Γ(X,U)) t) =
    Koszul.OrientedTopCohomology.ideal Γ(X,U) t := by
  change Ideal.span _ = Ideal.span _
  congr 1
  rw [Fin.elim0_append]
  have h : Function.Surjective (Fin.cast (Nat.zero_add m)) := by
    intro x
    exact ⟨Fin.cast (Nat.zero_add m).symm x, Fin.ext rfl⟩
  exact h.range_comp t

theorem weighted_of_kernel {k : Type u} [CommRing k] (η : Γ(X,U) →+* k)
    (hk : Koszul.OrientedTopCohomology.ideal Γ(X,U) t = RingHom.ker η)
    (z : Γ(X,U)) (hz : η z=1) (a : Γ(X,U)) :
    value U hU N ω t (z*a) = value U hU N ω t a := by
  rw [value_eq, value_eq]
  exact Koszul.FractionOrdinaryQuotient.Ordinary.weighted_of_kernel Γ(X,U) (SectionPresheaf.rings U hU)
    (PrincipalPoint.Fraction.family U t) (Fin.elim0 : Fin 0 → Γ(X,U)) t
    (PrincipalPoint.Fraction.units U hU t) (SectionPresheaf.modules U hU N) (multiplication U hU N ω)
    (fun _ j _ => Fin.elim0 j) η ((empty_parameters U t).trans hk) z hz a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrdinaryFraction.Ordinary
