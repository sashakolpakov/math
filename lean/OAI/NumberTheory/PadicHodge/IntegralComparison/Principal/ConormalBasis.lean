import OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedConormalBasisTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.IdealSheafPrincipalEquations

/-! # Conormal Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ConormalBasis

noncomputable section

/-! A matching conormal basis restricts to the matching basis for
the literal equations on an ambient principal open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {Y : Scheme.{u}} (I : Y.IdealSheafData) (U : Y.Opens)
  (hU : IsAffineOpen U) (r : Γ(Y, U))

variable {c : ℕ} (b : Module.Basis (Fin c) (Γ(Y, U) ⧸ I.ideal ⟨U,hU⟩)
  (I.ideal ⟨U,hU⟩).Cotangent)

def basis : Module.Basis (Fin c)
    (Γ(Y, Y.basicOpen r) ⧸ I.ideal ⟨Y.basicOpen r,hU.basicOpen r⟩)
    (I.ideal ⟨Y.basicOpen r,hU.basicOpen r⟩).Cotangent := by
  letI : IsLocalization.Away r Γ(Y, Y.basicOpen r) := hU.isLocalization_basicOpen r
  exact LocalizedConormalBasisTransport.Bases.conormalBasisOfEq r (I.ideal ⟨U,hU⟩)
    (I.ideal ⟨Y.basicOpen r,hU.basicOpen r⟩)
    (IdealSheafPrincipalEquations.ideal_map I U hU r) b

variable (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = I.ideal ⟨U,hU⟩)
  (hb : ∀ i, b i = (I.ideal ⟨U,hU⟩).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(Y, U) (I.ideal ⟨U,hU⟩) s hs i))

include hb in
theorem basis_apply (i : Fin c) : basis I U hU r b i =
    (I.ideal ⟨Y.basicOpen r,hU.basicOpen r⟩).toCotangent
      (ConormalKoszulPurity.conormalVectors Γ(Y, Y.basicOpen r)
        (I.ideal ⟨Y.basicOpen r,hU.basicOpen r⟩)
        (IdealSheafPrincipalEquations.sequence U r s)
        (IdealSheafPrincipalEquations.generates I U hU r s hs) i) := by
  let : IsLocalization.Away r Γ(Y, Y.basicOpen r) := hU.isLocalization_basicOpen r
  exact LocalizedConormalBasisTransport.Bases.conormalBasisOfEq_equations r (I.ideal ⟨U,hU⟩)
    (I.ideal ⟨Y.basicOpen r,hU.basicOpen r⟩)
    (IdealSheafPrincipalEquations.ideal_map I U hU r) b
    (ConormalKoszulPurity.conormalVectors Γ(Y, U) (I.ideal ⟨U,hU⟩) s hs) hb i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ConormalBasis
