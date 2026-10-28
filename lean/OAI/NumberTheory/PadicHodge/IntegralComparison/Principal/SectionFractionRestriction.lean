import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenTopClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrdinaryFractionScalar
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.TopClassCoefficients

/-! # Section Fraction Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionFractionRestriction

noncomputable section

/-! Restricting the original fractional section on the ambient principal
diagram gives the literal fractional section on the source diagram. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
open scoped BigOperators
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SymbolCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

section Units
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  {m : ℕ} (t : Fin m → Γ(X,U))

def unit (j : Fin m) : Γ(X,SectionPresheaf.openSubset U (PrincipalResidue.SymbolCoordinates.top U t))ˣ :=
  Cech.DenominatorUnits.coordinateUnit (PrincipalPoint.Fraction.family U t)
    (KoszulPartial.Fractions.rings Γ(X,U) (SectionPresheaf.rings U hU)) Γ(X,U)
    (KoszulPartial.Fractions.scalars Γ(X,U) (SectionPresheaf.rings U hU))
    (fun i => t i.down) (PrincipalPoint.Fraction.units U hU t)
    (AugmentedOrdered.CechCoordinates.topIndex m (by simp)) j

theorem unit_val (j : Fin m) : (unit U hU t j : Γ(X,SectionPresheaf.openSubset U (PrincipalResidue.SymbolCoordinates.top U t))) =
    X.presheaf.map (SectionPresheaf.inclusion U (PrincipalResidue.SymbolCoordinates.top U t)).op (t j) := by
  rw [unit, Cech.DenominatorUnits.coordinateUnit_val]
  change algebraMap Γ(X,U) Γ(X,SectionPresheaf.openSubset U (PrincipalResidue.SymbolCoordinates.top U t))
    (t ((AugmentedOrdered.CechCoordinates.topIndex (ι := ULift.{u} (Fin m)) m (by simp)).val j).down) = _
  rw [congrFun (Koszul.CechTopResidue.tuple_down (AugmentedOrdered.CechCoordinates.topIndex (ι := ULift.{u} (Fin m)) m (by simp))) j]
  rfl

theorem reciprocal_eq : OrdinaryFraction.Ordinary.reciprocal U hU t =
    (↑((∏ j, unit U hU t j)⁻¹) : Γ(X,SectionPresheaf.openSubset U (PrincipalResidue.SymbolCoordinates.top U t))) := rfl
end Units

variable {Y Z : Scheme.{u}} (π : Y ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U)
  (V : Y.Opens) (hV : IsAffineOpen V) (hVU : V ≤ π ⁻¹ᵁ U)
  (N : Y.Modules) (ω : Γ(N,π ⁻¹ᵁ U)) {m : ℕ} (t : Fin m → Γ(Z,U))

abbrev localSection := N.presheaf.map (homOfLE hVU).op ω

theorem coefficient (a : Γ(Z,U)) :
    PrincipalResidue.ResidueRestriction.coefficientMap π U V hV hVU t
      (PrincipalResidue.SymbolCoordinates.coefficient U hU t Γ(Z,U) a) =
    OrdinaryFraction.Ordinary.reciprocal V hV
        (PrincipalResidue.ResidueRestriction.parameters π U V hVU t) *
      algebraMap Γ(Y,V)
        Γ(Y,SectionPresheaf.openSubset V (PrincipalResidue.SymbolCoordinates.top V (PrincipalResidue.ResidueRestriction.parameters π U V hVU t)))
        (π.appLE U V hVU a) := by
  have h := PrincipalResidue.ResidueRestriction.coefficient π U hU V hV hVU t Γ(Z,U)
    (unit V hV (PrincipalResidue.ResidueRestriction.parameters π U V hVU t))
    (unit_val V hV (PrincipalResidue.ResidueRestriction.parameters π U V hVU t)) a
  rw [← reciprocal_eq] at h
  exact h.trans (mul_comm _ _)

def targetCoefficient (a : Γ(Z,U)) :
    Γ(N,SectionPresheaf.openSubset V (PrincipalResidue.SymbolCoordinates.top V (PrincipalResidue.ResidueRestriction.parameters π U V hVU t))) :=
  (OrdinaryFraction.Ordinary.multiplication V hV N (localSection π U V hVU N ω)).app
    (op (PrincipalResidue.SymbolCoordinates.top V (PrincipalResidue.ResidueRestriction.parameters π U V hVU t)))
    (OrdinaryFraction.Ordinary.reciprocal V hV
        (PrincipalResidue.ResidueRestriction.parameters π U V hVU t) *
      algebraMap Γ(Y,V)
        Γ(Y,SectionPresheaf.openSubset V (PrincipalResidue.SymbolCoordinates.top V (PrincipalResidue.ResidueRestriction.parameters π U V hVU t)))
        (π.appLE U V hVU a))

theorem symbol (a : Γ(Z,U)) :
    PrincipalSource.OpenTopClass.restriction π U V hV hVU N t
      (PrincipalResidue.SymbolCoordinates.symbolValue π U hU t Γ(Z,U) N ω a) =
    targetCoefficient π U V hV hVU N ω t a := by
  change N.presheaf.map (homOfLE (PrincipalResidue.ResidueRestriction.topBelow π U V hV hVU t)).op
    (π.app (SectionPresheaf.openSubset U (PrincipalResidue.SymbolCoordinates.top U t))
        (PrincipalResidue.SymbolCoordinates.coefficient U hU t Γ(Z,U) a) •
      N.presheaf.map (PushforwardSection.sourceInclusion π U (PrincipalResidue.SymbolCoordinates.top U t)).op ω) = _
  rw [N.map_smul]
  change PrincipalResidue.ResidueRestriction.coefficientMap π U V hV hVU t
      (PrincipalResidue.SymbolCoordinates.coefficient U hU t Γ(Z,U) a) •
    N.presheaf.map (homOfLE (PrincipalResidue.ResidueRestriction.topBelow π U V hV hVU t)).op
      (N.presheaf.map (PushforwardSection.sourceInclusion π U (PrincipalResidue.SymbolCoordinates.top U t)).op ω) = _
  rw [coefficient]
  let b : Γ(Y,SectionPresheaf.openSubset V (PrincipalResidue.SymbolCoordinates.top V (PrincipalResidue.ResidueRestriction.parameters π U V hVU t))) :=
    OrdinaryFraction.Ordinary.reciprocal V hV
      (PrincipalResidue.ResidueRestriction.parameters π U V hVU t) *
      algebraMap Γ(Y,V) _ (π.appLE U V hVU a)
  change b • N.presheaf.map
      (homOfLE (PrincipalResidue.ResidueRestriction.topBelow π U V hV hVU t)).op
      (N.presheaf.map (PushforwardSection.sourceInclusion π U (PrincipalResidue.SymbolCoordinates.top U t)).op ω) =
    b • N.presheaf.map (SectionPresheaf.inclusion V
      (PrincipalResidue.SymbolCoordinates.top V (PrincipalResidue.ResidueRestriction.parameters π U V hVU t))).op
      (N.presheaf.map (homOfLE hVU).op ω)
  congr 1
  rw [← ConcreteCategory.comp_apply, ← N.presheaf.map_comp,
    ← ConcreteCategory.comp_apply, ← N.presheaf.map_comp]
  rfl

def targetIso := AugmentedCech.TopClassCoefficients.homologyIso
  (PrincipalPoint.Fraction.family V (PrincipalResidue.ResidueRestriction.parameters π U V hVU t))
  (AdditiveSections.forgetScalars V) (SectionPresheaf.modules V hV N) m

theorem class_coordinate (a : Γ(Z,U)) :
    (targetIso π U V hV hVU N t).hom
      (OrdinaryFraction.Ordinary.value V hV N (localSection π U V hVU N ω)
        (PrincipalResidue.ResidueRestriction.parameters π U V hVU t) (π.appLE U V hVU a)) =
    AugmentedCech.TopClassMap.map
      (PrincipalPoint.Fraction.family V (PrincipalResidue.ResidueRestriction.parameters π U V hVU t))
      (PrincipalSource.OpenTopClass.target V hV N) m (by simp)
      (targetCoefficient π U V hV hVU N ω t a) := by
  have h := ConcreteCategory.congr_hom
    (AugmentedCech.TopClassCoefficients.comparison
      (PrincipalPoint.Fraction.family V (PrincipalResidue.ResidueRestriction.parameters π U V hVU t))
      (AdditiveSections.forgetScalars V) (SectionPresheaf.modules V hV N) m (by simp))
    (targetCoefficient π U V hV hVU N ω t a)
  change (targetIso π U V hV hVU N t).hom
      (AugmentedCech.TopClassMap.map
        (PrincipalPoint.Fraction.family V (PrincipalResidue.ResidueRestriction.parameters π U V hVU t))
        (SectionPresheaf.modules V hV N) m (by simp) (targetCoefficient π U V hV hVU N ω t a)) = _ at h
  rw [AugmentedCech.TopClassMap.module_apply] at h
  exact h

theorem comparison (a : Γ(Z,U)) :
    homologyMap (PrincipalSource.OpenTopClass.complexMap π U hU V hV hVU N t) m
      (AugmentedCech.TopClassMap.map (PrincipalPoint.Fraction.family U t)
        (PrincipalSource.OpenTopClass.source π U hU N) m (by simp)
        (PrincipalResidue.SymbolCoordinates.symbolValue π U hU t Γ(Z,U) N ω a)) =
    (targetIso π U V hV hVU N t).hom
      (OrdinaryFraction.Ordinary.value V hV N (localSection π U V hVU N ω)
        (PrincipalResidue.ResidueRestriction.parameters π U V hVU t) (π.appLE U V hVU a)) := by
  rw [PrincipalSource.OpenTopClass.apply, symbol]
  exact (class_coordinate π U V hV hVU N ω t a).symm

theorem weighted {k : Type u} [CommRing k] (η : Γ(Y,V) →+* k)
    (hk : Koszul.OrientedTopCohomology.ideal Γ(Y,V)
      (PrincipalResidue.ResidueRestriction.parameters π U V hVU t) = RingHom.ker η)
    (z : Γ(Y,V)) (hz : η z = 1) (ω₀ : Γ(N,V))
    (hω : localSection π U V hVU N ω = z • ω₀) (a : Γ(Z,U)) :
    homologyMap (PrincipalSource.OpenTopClass.complexMap π U hU V hV hVU N t) m
      (AugmentedCech.TopClassMap.map (PrincipalPoint.Fraction.family U t)
        (PrincipalSource.OpenTopClass.source π U hU N) m (by simp)
        (PrincipalResidue.SymbolCoordinates.symbolValue π U hU t Γ(Z,U) N ω a)) =
    (targetIso π U V hV hVU N t).hom
      (OrdinaryFraction.Ordinary.value V hV N ω₀
        (PrincipalResidue.ResidueRestriction.parameters π U V hVU t) (π.appLE U V hVU a)) := by
  rw [comparison, hω, OrdinaryFractionScalar.Ordinary.section_weighted_of_kernel V hV N ω₀
    (PrincipalResidue.ResidueRestriction.parameters π U V hVU t) η hk z hz]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionFractionRestriction
