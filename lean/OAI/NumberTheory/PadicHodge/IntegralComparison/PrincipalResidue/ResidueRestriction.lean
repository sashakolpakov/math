import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SymbolCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenReindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.ReciprocalTransport

/-! # Residue Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.ResidueRestriction

noncomputable section

/-! Restriction of the original scalar fraction to the genuine source
principal diagram. The coefficient map is the actual scheme appLE,
and the denominator is transported through the canonical top product. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped BigOperators
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SymbolCoordinates
variable {X Y : Scheme.{u}} (π : X ⟶ Y)
  (U : Y.Opens) (hU : IsAffineOpen U)
  (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ π ⁻¹ᵁ U)
  {m : ℕ} (t : Fin m → Γ(Y,U))

def parameters : Fin m → Γ(X,V) := fun j => π.appLE U V hVU (t j)

def topIso :
    (PrincipalSource.OpenReindex.reindex π U V hVU).obj (SymbolCoordinates.top U t) ≅
      SymbolCoordinates.top V (parameters π U V hVU t) :=
  AugmentedOrdered.CechReindexTop.objectIso
    (PrincipalSource.OpenReindex.reindex π U V hVU)
    (PrincipalPoint.Fraction.family U t) m (by simp)

include hV in
theorem topOpen_eq :
    Principal.SectionPresheaf.openSubset V (SymbolCoordinates.top V (parameters π U V hVU t)) =
      V ⊓ π ⁻¹ᵁ (Principal.SectionPresheaf.openSubset U (SymbolCoordinates.top U t)) := by
  have e := (Principal.AdditiveSections.opens V hV).mapIso (topIso π U V hVU t)
  have he : Principal.SectionPresheaf.openSubset V (SymbolCoordinates.top V (parameters π U V hVU t)) =
      Principal.SectionPresheaf.openSubset V ((PrincipalSource.OpenReindex.reindex π U V hVU).obj (SymbolCoordinates.top U t)) :=
    le_antisymm (leOfHom e.inv) (leOfHom e.hom)
  exact he.trans (PrincipalSource.OpenReindex.open_eq π U V hV hVU (SymbolCoordinates.top U t))

include hV in
theorem topBelow :
    Principal.SectionPresheaf.openSubset V (SymbolCoordinates.top V (parameters π U V hVU t)) ≤ π ⁻¹ᵁ (Principal.SectionPresheaf.openSubset U (SymbolCoordinates.top U t)) := by
  rw [topOpen_eq π U V hV hVU t]
  exact inf_le_right

def coefficientMap : Γ(Y,Principal.SectionPresheaf.openSubset U (SymbolCoordinates.top U t)) →+*
    Γ(X,Principal.SectionPresheaf.openSubset V (SymbolCoordinates.top V (parameters π U V hVU t))) :=
  (π.appLE (Principal.SectionPresheaf.openSubset U (SymbolCoordinates.top U t)) (Principal.SectionPresheaf.openSubset V (SymbolCoordinates.top V (parameters π U V hVU t)))
    (topBelow π U V hV hVU t)).hom

theorem map_restriction (b : Γ(Y,U)) :
    coefficientMap π U V hV hVU t
        (algebraMap Γ(Y,U) Γ(Y,Principal.SectionPresheaf.openSubset U (SymbolCoordinates.top U t)) b) =
      X.presheaf.map (Principal.SectionPresheaf.inclusion V (SymbolCoordinates.top V (parameters π U V hVU t))).op
        (π.appLE U V hVU b) := by
  have hleft := ConcreteCategory.congr_hom
    (π.map_appLE (topBelow π U V hV hVU t) (Principal.SectionPresheaf.inclusion U (SymbolCoordinates.top U t)).op) b
  have hright := ConcreteCategory.congr_hom
    (π.appLE_map hVU (Principal.SectionPresheaf.inclusion V (SymbolCoordinates.top V (parameters π U V hVU t))).op) b
  exact hleft.trans hright.symm

variable (k : Type u) [CommRing k] [Algebra k Γ(Y,U)]
  (units : Fin m → Γ(X,Principal.SectionPresheaf.openSubset V (SymbolCoordinates.top V (parameters π U V hVU t)))ˣ)
  (hunits : ∀ j, (units j : Γ(X,Principal.SectionPresheaf.openSubset V (SymbolCoordinates.top V (parameters π U V hVU t)))) =
    X.presheaf.map (Principal.SectionPresheaf.inclusion V (SymbolCoordinates.top V (parameters π U V hVU t))).op
      (parameters π U V hVU t j))

include hunits in
theorem coefficient (a : k) :
    coefficientMap π U V hV hVU t (SymbolCoordinates.coefficient U hU t k a) =
      X.presheaf.map (Principal.SectionPresheaf.inclusion V (SymbolCoordinates.top V (parameters π U V hVU t))).op
        (π.appLE U V hVU (algebraMap k Γ(Y,U) a)) * (↑((∏ j, units j)⁻¹) :
          Γ(X,Principal.SectionPresheaf.openSubset V (SymbolCoordinates.top V (parameters π U V hVU t)))) := by
  have hunit (j : Fin m) : coefficientMap π U V hV hVU t
      (algebraMap Γ(Y,U) Γ(Y,Principal.SectionPresheaf.openSubset U (SymbolCoordinates.top U t)) (t j)) = (units j : _) :=
    (map_restriction π U V hV hVU t (t j)).trans (hunits j).symm
  have hr := KoszulPartial.ReciprocalTransport.top_reciprocal_map
    Γ(Y,U) (Principal.SectionPresheaf.rings U hU) (PrincipalPoint.Fraction.family U t) t
    (PrincipalPoint.Fraction.units U hU t) (by simp)
    (coefficientMap π U V hV hVU t) units hunit
  change coefficientMap π U V hV hVU t (_ * _) = _
  rw [map_mul]
  exact (congrArg₂ (fun (x y : Γ(X,Principal.SectionPresheaf.openSubset V (SymbolCoordinates.top V (parameters π U V hVU t)))) => x*y)
    hr (map_restriction π U V hV hVU t (algebraMap k Γ(Y,U) a))).trans (mul_comm _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.ResidueRestriction
