import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicEstimates
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm

/-! # Weak Admissibility Bridge -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.WeakAdmissibilityBridge

noncomputable section

/-!
# Bridge between the independently constructed PeriodInvariants and WeakAdmissibility envelopes

The equality here is proved from the actual divided-power generators. It is
not an assumption identifying opaque period-ring interfaces. The bridge is
kept separate from both foundational modules to avoid cyclic imports.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicEstimates.Frobenius

variable (p : ℕ) [Fact p.Prime]

/-- The two constructions define the same uncompleted divided-power subalgebra. -/
theorem envelopes_eq : WeakAdmissibility.Logarithm.PeriodRings.aCrisUncompleted p =
    PeriodRing.acrisZeroSubalgebra p := by
  change AdicEstimates.Frobenius.modPEnvelope p = PeriodRing.acrisZeroSubalgebra p
  exact AdicEstimates.Frobenius.modPEnvelope_eq_acrisZero p

def uncompletedEquiv : WeakAdmissibility.Logarithm.PeriodRings.ACrisUncompleted p ≃+* PeriodRing.AcrisZero p :=
  (Subalgebra.equivOfEq _ _ (envelopes_eq p)).toRingEquiv

section Transport

variable {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]

theorem subalgebraEquivOfEq_coe (S T : Subalgebra A L) (h : S = T) (x : S) :
    ((Subalgebra.equivOfEq S T h).toRingEquiv x : L) = x := rfl

/-- Completion respects equality of the concrete coefficient subalgebras. -/
def completedSubalgebraEquiv (S T : Subalgebra A L) (h : S = T) :
    AdicCompletion (Ideal.span {(p : S)}) S ≃+*
      AdicCompletion (Ideal.span {(p : T)}) T := by
  subst T
  exact RingEquiv.refl _

def positiveSubalgebraEquiv (S T : Subalgebra A L) (h : S = T) :
    Localization.Away (p : AdicCompletion (Ideal.span {(p : S)}) S) ≃+*
      Localization.Away (p : AdicCompletion (Ideal.span {(p : T)}) T) := by
  subst T
  exact RingEquiv.refl _

end Transport

theorem ringHom_comp_equiv_surjective {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    (f : S →+* T) (e : R ≃+* S) (hf : Function.Surjective f) :
    Function.Surjective (f.comp e.toRingHom) := hf.comp e.surjective

theorem ringEquiv_nontrivial {R S : Type*} [CommRing R] [CommRing S]
    [Nontrivial S] (e : R ≃+* S) : Nontrivial R := e.surjective.nontrivial

/-- The two actual completed integral period rings are isomorphic. -/
def acrisEquiv : WeakAdmissibility.Logarithm.PeriodRings.ACris p ≃+* PeriodRing.Acris p :=
  completedSubalgebraEquiv p _ _ (envelopes_eq p)

/-- The two actual positive crystalline period rings are isomorphic. -/
def bcrisPlusEquiv : WeakAdmissibility.Logarithm.PeriodRings.BCrisPlus p ≃+* PeriodRing.BcrisPlus p :=
  positiveSubalgebraEquiv p _ _ (envelopes_eq p)

theorem ainfFrobenius_eq : WeakAdmissibility.Logarithm.PeriodRings.aInfFrobenius p =
    AdicEstimates.Frobenius.ainfFrobenius p := rfl

theorem fractionFrobenius_eq (x : FractionRing (PeriodRing.Ainf p)) :
    WeakAdmissibility.Logarithm.PeriodRings.fractionFrobenius p x =
      AdicEstimates.Frobenius.fractionFrobenius p x := by
  have h : WeakAdmissibility.Logarithm.PeriodRings.fractionFrobenius p =
      AdicEstimates.Frobenius.fractionFrobenius p :=
    congrArg (fun e : PeriodRing.Ainf p ≃+* PeriodRing.Ainf p =>
      IsFractionRing.ringEquivOfRingEquiv (K := FractionRing (PeriodRing.Ainf p))
        (L := FractionRing (PeriodRing.Ainf p)) e) (ainfFrobenius_eq p)
  exact DFunLike.congr_fun h x

theorem uncompletedEquiv_coe (x : WeakAdmissibility.Logarithm.PeriodRings.ACrisUncompleted p) :
    (uncompletedEquiv p x : FractionRing (PeriodRing.Ainf p)) = x :=
  subalgebraEquivOfEq_coe _ _ (envelopes_eq p) x

theorem e63Frobenius_coe (x : WeakAdmissibility.Logarithm.PeriodRings.ACrisUncompleted p) :
    (WeakAdmissibility.Logarithm.PeriodRings.aCrisUncompletedFrobenius p x : FractionRing (PeriodRing.Ainf p)) =
      WeakAdmissibility.Logarithm.PeriodRings.fractionFrobenius p x := rfl

theorem e61Frobenius_coe (x : PeriodRing.AcrisZero p) :
    (AdicEstimates.Frobenius.acrisZeroFrobenius p x : FractionRing (PeriodRing.Ainf p)) =
      AdicEstimates.Frobenius.fractionFrobenius p x := rfl

theorem uncompletedEquiv_frobenius (x : WeakAdmissibility.Logarithm.PeriodRings.ACrisUncompleted p) :
    uncompletedEquiv p (WeakAdmissibility.Logarithm.PeriodRings.aCrisUncompletedFrobenius p x) =
      AdicEstimates.Frobenius.acrisZeroFrobenius p (uncompletedEquiv p x) := by
  apply Subtype.val_injective
  rw [uncompletedEquiv_coe, e63Frobenius_coe, e61Frobenius_coe, uncompletedEquiv_coe]
  exact fractionFrobenius_eq p x

/-- The proved integral theta map transfers through the concrete bridge. -/
def thetaWeakAdmissibilityAcris : WeakAdmissibility.Logarithm.PeriodRings.ACris p →+* 𝓞_ℂ_[p] :=
  (Nontriviality.thetaAcris p).comp (acrisEquiv p).toRingHom

theorem thetaWeakAdmissibilityAcris_surjective : Function.Surjective (thetaWeakAdmissibilityAcris p) :=
  ringHom_comp_equiv_surjective (Nontriviality.thetaAcris p) (acrisEquiv p) (Nontriviality.thetaAcris_surjective p)

theorem e63_acris_nontrivial : Nontrivial (WeakAdmissibility.Logarithm.PeriodRings.ACris p) :=
  ringEquiv_nontrivial (acrisEquiv p)

theorem e63_bcrisPlus_nontrivial : Nontrivial (WeakAdmissibility.Logarithm.PeriodRings.BCrisPlus p) :=
  ringEquiv_nontrivial (bcrisPlusEquiv p)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.WeakAdmissibilityBridge
