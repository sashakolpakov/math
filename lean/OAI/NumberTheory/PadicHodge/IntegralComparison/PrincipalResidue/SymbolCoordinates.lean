import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedResidueSingleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Fraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSection

/-! # Symbol Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SymbolCoordinates

noncomputable section

/-! The coefficient of the original scalar residue becomes the literal
fractional section under the actual principal multiplication map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (U : Y.Opens) (hU : IsAffineOpen U) {c m : ℕ} (s : Fin c → Γ(Y,U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y,U) s = f.ker.ideal ⟨U,hU⟩)
  (t : Fin m → Γ(Y,U)) (k : Type u) [CommRing k] [Algebra k Γ(Y,U)]

private theorem cardinal : Fintype.card (ULift.{u} (Fin m)) = m := by simp
abbrev top := AugmentedOrdered.CechCoordinates.topObject (PrincipalPoint.Fraction.family U t) m (cardinal (m := m))

def coefficient (a : k) : Γ(Y, Principal.SectionPresheaf.openSubset U (top U t)) :=
  (show Γ(Y, Principal.SectionPresheaf.openSubset U (top U t)) from
    KoszulPartial.Fractions.reciprocal Γ(Y,U) (Principal.SectionPresheaf.rings U hU)
      (PrincipalPoint.Fraction.family U t) t (PrincipalPoint.Fraction.units U hU t)
      (AugmentedOrdered.CechCoordinates.topIndex m (cardinal (m := m)))) *
      algebraMap Γ(Y,U) Γ(Y,Principal.SectionPresheaf.openSubset U (top U t)) (algebraMap k Γ(Y,U) a)

def value (a : k) := Koszul.RefinedResidueSingleCoordinates.scalarValue
  Γ(Y,U) (Principal.SectionPresheaf.rings U hU) (PrincipalPoint.Fraction.family U t) t
  (PrincipalPoint.Fraction.units U hU t) (Principal.ClosedKoszulResidue.target f U hU)
  (Principal.ClosedKoszulResidue.pullback f U hU s hs) k a

theorem value_eq (a : k) : value f U hU s hs t k a =
    f.app (Principal.SectionPresheaf.openSubset U (top U t)) (coefficient U hU t k a) := by
  exact Principal.ClosedKoszulResidue.pullback_apply f U hU s hs
    (op (top U t)) (coefficient U hU t k a)

variable (N : X.Modules) (ω : Γ(N, f ⁻¹ᵁ U))

def symbolValue (a : k) : Γ(N, f ⁻¹ᵁ Principal.SectionPresheaf.openSubset U (top U t)) :=
  f.app (Principal.SectionPresheaf.openSubset U (top U t)) (coefficient U hU t k a) •
    N.presheaf.map (Principal.PushforwardSection.sourceInclusion f U (top U t)).op ω

theorem symbol (a : k) :
    (Principal.PushforwardSection.map f U hU N ω).app (op (top U t))
      (value f U hU s hs t k a) = symbolValue f U hU t k N ω a := by
  change (show Γ(X, f ⁻¹ᵁ Principal.SectionPresheaf.openSubset U (top U t)) from value f U hU s hs t k a) •
    N.presheaf.map (Principal.PushforwardSection.sourceInclusion f U (top U t)).op ω = _
  rw [value_eq]
  rfl

theorem ordinary_symbol (a : k) :
    homologyMap (AugmentedOrdered.CechFunctor.complexMap (PrincipalPoint.Fraction.family U t)
      (Principal.PushforwardSection.map f U hU N ω)) m
      (AugmentedOrdered.CechTopClass.topClass (PrincipalPoint.Fraction.family U t)
        (Principal.ClosedKoszulResidue.target f U hU) m (cardinal (m := m))
        (value f U hU s hs t k a)) =
    AugmentedOrdered.CechTopClass.topClass (PrincipalPoint.Fraction.family U t)
      (Principal.SectionPresheaf.modules U hU ((Scheme.Modules.pushforward f).obj N)) m (cardinal (m := m))
      (symbolValue f U hU t k N ω a) := by
  rw [AugmentedOrdered.CechTopClass.topClass_naturality, symbol]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SymbolCoordinates
