import OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedParameterBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.IdealSheafPrincipalEquations
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction

/-! # Quotient Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.QuotientBasis

noncomputable section

/-! The quotient differential basis on a principal open is matched to
the literal restrictions of the original ambient parameter lifts. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (Y : Over (Spec (CommRingCat.of R)))
  (I : Y.left.IdealSheafData) (U : Y.left.Opens) (hU : IsAffineOpen U) (r : Γ(Y.left, U))

local instance baseAlgebra (V : Y.left.Opens) : Algebra R Γ(Y.left, V) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y V
local instance scalarTower : IsScalarTower R Γ(Y.left, U) Γ(Y.left, Y.left.basicOpen r) :=
  IsScalarTower.of_algebraMap_eq (fun a =>
    (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y).map
      (homOfLE (Y.left.basicOpen_le r)).op).hom.commutes a).symm)

variable {g : ℕ} (b : Module.Basis (Fin g) (Γ(Y.left, U) ⧸ I.ideal ⟨U,hU⟩)
  Ω[Γ(Y.left, U) ⧸ I.ideal ⟨U,hU⟩⁄R])

def basis : Module.Basis (Fin g)
    (Γ(Y.left, Y.left.basicOpen r) ⧸ I.ideal ⟨Y.left.basicOpen r,hU.basicOpen r⟩)
    Ω[Γ(Y.left, Y.left.basicOpen r) ⧸ I.ideal ⟨Y.left.basicOpen r,hU.basicOpen r⟩⁄R] := by
  letI : IsLocalization.Away r Γ(Y.left, Y.left.basicOpen r) := hU.isLocalization_basicOpen r
  exact LocalizedConormalBasisTransport.Bases.quotientBasisOfEq r (I.ideal ⟨U,hU⟩)
    (I.ideal ⟨Y.left.basicOpen r,hU.basicOpen r⟩)
    (IdealSheafPrincipalEquations.ideal_map I U hU r) b

variable (t : Fin g → Γ(Y.left, U))
  (hb : ∀ i, b i = KaehlerDifferential.D R (Γ(Y.left, U) ⧸ I.ideal ⟨U,hU⟩)
    (Ideal.Quotient.mk _ (t i)))

include hb in
theorem basis_apply (i : Fin g) : basis R Y I U hU r b i =
    KaehlerDifferential.D R (Γ(Y.left, Y.left.basicOpen r) ⧸
      I.ideal ⟨Y.left.basicOpen r,hU.basicOpen r⟩)
      (Ideal.Quotient.mk _ (IdealSheafPrincipalEquations.sequence U r t i)) := by
  let : IsLocalization.Away r Γ(Y.left, Y.left.basicOpen r) := hU.isLocalization_basicOpen r
  exact LocalizedParameterBasis.ConormalBases.quotientBasisOfEq_equations r (I.ideal ⟨U,hU⟩) b t hb
    (I.ideal ⟨Y.left.basicOpen r,hU.basicOpen r⟩)
    (IdealSheafPrincipalEquations.ideal_map I U hU r) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.QuotientBasis
