import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteFieldLift
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ComplexResidueP

/-! # Tilt Constants -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.TiltConstants

noncomputable section

/-!
# Finite residue-field constants in the actual tilt of O_Cp

A finite field embedded in the residue field lifts canonically to O_Cp/p.
The universal property of perfection then lifts it to the tilt. Both maps
are injective and natural for automorphisms of O_Cp.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.ComplexResidueP

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Fintype k] [CharP k p]

def modPConstants (κ : k →+* ComplexResidueP.ComplexResidue p) : k →+* ModP 𝓞_ℂ_[p] p :=
  FiniteFieldLift.lift p k (ComplexResidueP.modPResidue p) (ComplexResidueP.modPResidue_surjective p) (ComplexResidueP.modPResidue_nil_kernel p) κ

theorem modPConstants_residue (κ : k →+* ComplexResidueP.ComplexResidue p) (a : k) :
    ComplexResidueP.modPResidue p (modPConstants p k κ a) = κ a :=
  FiniteFieldLift.lift_spec p k (ComplexResidueP.modPResidue p)
    (ComplexResidueP.modPResidue_surjective p) (ComplexResidueP.modPResidue_nil_kernel p) κ a

theorem modPConstants_injective (κ : k →+* ComplexResidueP.ComplexResidue p) :
    Function.Injective (modPConstants p k κ) := by
  intro a b hab
  apply κ.injective
  rw [← modPConstants_residue p k κ a, ← modPConstants_residue p k κ b, hab]

def tiltConstants (κ : k →+* ComplexResidueP.ComplexResidue p) : k →+* PreTilt 𝓞_ℂ_[p] p :=
  Perfection.lift p k (ModP 𝓞_ℂ_[p] p) (modPConstants p k κ)

theorem tiltConstants_coeff_zero (κ : k →+* ComplexResidueP.ComplexResidue p) (a : k) :
    Perfection.coeff (ModP 𝓞_ℂ_[p] p) p 0 (tiltConstants p k κ a) = modPConstants p k κ a := rfl

theorem tiltConstants_injective (κ : k →+* ComplexResidueP.ComplexResidue p) :
    Function.Injective (tiltConstants p k κ) := by
  intro a b hab
  apply modPConstants_injective p k κ
  exact congrArg (Perfection.coeff (ModP 𝓞_ℂ_[p] p) p 0) hab

theorem modPResidue_natural (e : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : ModP 𝓞_ℂ_[p] p) :
    ComplexResidueP.modPResidue p (PeriodRing.modPMap p e.toRingHom x) =
      IsLocalRing.ResidueField.map e.toRingHom (ComplexResidueP.modPResidue p x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [PeriodRing.modPMap_mk, ComplexResidueP.modPResidue_mk, ComplexResidueP.modPResidue_mk]
  exact (IsLocalRing.ResidueField.map_residue e.toRingHom a).symm

theorem modPConstants_natural (κ : k →+* ComplexResidueP.ComplexResidue p) (e : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (a : k) :
    PeriodRing.modPMap p e.toRingHom (modPConstants p k κ a) =
      modPConstants p k ((IsLocalRing.ResidueField.map e.toRingHom).comp κ) a :=
  FiniteFieldLift.lift_natural p k (ComplexResidueP.modPResidue p)
    (ComplexResidueP.modPResidue_surjective p) (ComplexResidueP.modPResidue_nil_kernel p) κ
    (PeriodRing.modPMap p e.toRingHom) (IsLocalRing.ResidueField.map e.toRingHom) (modPResidue_natural p e) a

theorem tiltConstants_natural (κ : k →+* ComplexResidueP.ComplexResidue p) (e : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (a : k) :
    PeriodRing.tiltMap p e.toRingHom (tiltConstants p k κ a) =
      tiltConstants p k ((IsLocalRing.ResidueField.map e.toRingHom).comp κ) a := by
  have he : (PeriodRing.tiltMap p e.toRingHom).comp (tiltConstants p k κ) =
      tiltConstants p k ((IsLocalRing.ResidueField.map e.toRingHom).comp κ) := by
    apply Perfection.hom_ext
    intro x
    exact modPConstants_natural p k κ e x
  exact DFunLike.congr_fun he a

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.TiltConstants
