import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SymbolCoordinates

/-! # Symbol Pushforward -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SymbolPushforward

noncomputable section

/-! A fractional section of an actual pushforward has the same
literal section value for the composite scheme morphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (i : X ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U) {m : ℕ} (t : Fin m → Γ(Z,U))
  (R : Type u) [CommRing R] [Algebra R Γ(Z,U)] (N : Y.Modules)
  (ω : Γ(N, f ⁻¹ᵁ (i ⁻¹ᵁ U))) (a : R)

theorem symbol :
    PrincipalResidue.SymbolCoordinates.symbolValue i U hU t R
      ((Scheme.Modules.pushforward f).obj N) ω a =
    PrincipalResidue.SymbolCoordinates.symbolValue (f ≫ i) U hU t R N ω a := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SymbolPushforward
