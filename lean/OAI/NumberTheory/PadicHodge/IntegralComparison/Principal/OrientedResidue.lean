import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Koszul
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedKoszulResidue

/-! # Oriented Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidue

noncomputable section

/-! A canonical normal-residue representative on the original
internal-Hom principal section complex. It uses the actual augmented
sheaf resolution, the original closed-scheme quotient, and one ambient
line frame, followed by the ordered normal-Koszul residue. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj (ClosedQuotient.directImage f))
  [QuasiIso ε] [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))

local instance structure_quasicoherent : (ClosedQuotient.directImage f).IsQuasicoherent := by
  let : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  exact AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f

def quotientIso : (AffineOpen.InternalHom.sections U hU).obj (ClosedQuotient.directImage f) ≅
    ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Y, U) s) :=
  Closed.QuotientSectionNormalization.chartIso f U hU ≪≫
    (Ideal.quotientEquivAlgOfEq Γ(Y, U) hs.symm).toLinearEquiv.toModuleIso

def map : Koszul.Comparison.nativeComplex U hU N K ⟶
    (single ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat Γ(Y, U)) (.up ℕ) c).obj
      (ClosedKoszulResidue.target f U hU) :=
  (Koszul.Comparison.equivalence U hU N e K
    (ClosedQuotient.directImage f) ε s hreg (quotientIso f U hU s hs)).hom ≫
      ClosedKoszulResidue.residue f U hU s hs

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidue
