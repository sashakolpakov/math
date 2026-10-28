import OAI.NumberTheory.PadicHodge.PeriodInvariants.WeakAdmissibilityBridge
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CompletionMaps
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm

/-! # Cyclotomic -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.Cyclotomic

noncomputable section

/-!
# Cyclotomic logarithm and Frobenius on PeriodInvariants's crystalline period ring

The logarithm identity is transported through the proved equality of the
concrete envelopes. All period elements use PeriodInvariants's chosen compatible roots.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicEstimates.Frobenius OAI.NumberTheory.PadicHodge.PeriodInvariants.CompletionMaps

theorem pAdicBetweenEquiv_subalgebra (p : ℕ)
    {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]
    (S T : Subalgebra A L) (h : S = T) :
    CompletionMaps.pAdicBetweenEquiv p (Subalgebra.equivOfEq S T h).toRingEquiv =
      WeakAdmissibilityBridge.completedSubalgebraEquiv p S T h := by
  subst T
  apply RingEquiv.toRingHom_injective
  exact CompletionMaps.pAdicBetween_id p

theorem completionMap_eq_pAdicMap (p : ℕ) {R : Type*} [CommRing R]
    (f : R →+* R) (hf : (Ideal.span {(p : R)}).map f ≤ Ideal.span {(p : R)}) :
    WeakAdmissibility.Logarithm.PeriodRings.completionMap (Ideal.span {(p : R)}) f hf = PeriodRing.pAdicMap p f := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [WeakAdmissibility.Logarithm.PeriodRings.completionMap, AdicCompletion.evalₐ_liftRingHom, PeriodRing.pAdicMap_eval]
  rfl

theorem ringEquiv_transport_nat_mul {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a b : R) (c d : S) (n : ℕ)
    (ha : e a = c) (hb : e b = d) (h : a = (n : R) * b) : c = (n : S) * d := by
  rw [← ha, ← hb, h, map_mul, map_natCast]

variable (p : ℕ) [Fact p.Prime]

/-- The completed envelope comparison, defined on each quotient ring. -/
def acrisComparison : WeakAdmissibility.Logarithm.PeriodRings.ACris p ≃+* PeriodRing.Acris p :=
  CompletionMaps.pAdicBetweenEquiv p (WeakAdmissibilityBridge.uncompletedEquiv p)

/-- The direct quotient construction is the already proved ring identification. -/
theorem acrisComparison_eq : acrisComparison p = WeakAdmissibilityBridge.acrisEquiv p :=
  pAdicBetweenEquiv_subalgebra p (WeakAdmissibility.Logarithm.PeriodRings.aCrisUncompleted p)
    (PeriodRing.acrisZeroSubalgebra p) (WeakAdmissibilityBridge.envelopes_eq p)

theorem e63Frobenius_eq_pAdicMap : WeakAdmissibility.Logarithm.PeriodRings.aCrisFrobenius p =
    PeriodRing.pAdicMap p (WeakAdmissibility.Logarithm.PeriodRings.aCrisUncompletedFrobenius p) :=
  completionMap_eq_pAdicMap p (WeakAdmissibility.Logarithm.PeriodRings.aCrisUncompletedFrobenius p)
    (WeakAdmissibility.Logarithm.PeriodRings.aCrisUncompletedFrobenius_preserves_p p)

theorem acrisComparison_frobenius (x : WeakAdmissibility.Logarithm.PeriodRings.ACris p) :
    acrisComparison p (WeakAdmissibility.Logarithm.PeriodRings.aCrisFrobenius p x) =
      AdicEstimates.Frobenius.acrisFrobenius p (acrisComparison p x) := by
  rw [e63Frobenius_eq_pAdicMap]
  exact CompletionMaps.pAdicBetween_natural p (WeakAdmissibilityBridge.uncompletedEquiv p).toRingHom
    (WeakAdmissibility.Logarithm.PeriodRings.aCrisUncompletedFrobenius p) (AdicEstimates.Frobenius.acrisZeroFrobenius p)
    (WeakAdmissibilityBridge.uncompletedEquiv_frobenius p) x

theorem kernel_modP (x : RingHom.ker (PeriodRing.theta p)) : WeakAdmissibility.Logarithm.PeriodRings.thetaModP p x = 0 := by
  change Ideal.Quotient.mk _ (PeriodRing.theta p x) = 0
  rw [RingHom.mem_ker.mp x.property, map_zero]

theorem uncompletedEquiv_dividedPower (x : RingHom.ker (PeriodRing.theta p)) (n : ℕ) :
    WeakAdmissibilityBridge.uncompletedEquiv p
        (WeakAdmissibility.Logarithm.PeriodRings.dividedPower p x n (kernel_modP p x)) = PeriodRing.dividedPower p n x := by
  apply Subtype.val_injective
  rw [WeakAdmissibilityBridge.uncompletedEquiv_coe, PeriodRing.dividedPower_coe]
  rfl

theorem uncompletedEquiv_logTerm (x : RingHom.ker (PeriodRing.theta p)) (n : ℕ) :
    WeakAdmissibilityBridge.uncompletedEquiv p
        (WeakAdmissibility.Logarithm.PeriodRings.crystallineLogTerm p x (kernel_modP p x) n) = PeriodRing.logTerm p x n := by
  simp only [WeakAdmissibility.Logarithm.PeriodRings.crystallineLogTerm, PeriodRing.logTerm, map_mul, map_pow,
    map_neg, map_one, map_natCast, uncompletedEquiv_dividedPower]

theorem acrisComparison_eval (x : WeakAdmissibility.Logarithm.PeriodRings.ACris p) (n : ℕ) :
    AdicCompletion.evalₐ (Ideal.span {(p : PeriodRing.AcrisZero p)}) n (acrisComparison p x) =
      Nontriviality.pPowerMapBetween p (WeakAdmissibilityBridge.uncompletedEquiv p).toRingHom n
        (AdicCompletion.evalₐ (Ideal.span {(p : WeakAdmissibility.Logarithm.PeriodRings.ACrisUncompleted p)}) n x) :=
  CompletionMaps.pAdicBetween_eval p (WeakAdmissibilityBridge.uncompletedEquiv p).toRingHom x n

theorem acrisComparison_log (x : RingHom.ker (PeriodRing.theta p)) :
    acrisComparison p
        (WeakAdmissibility.Logarithm.PeriodRings.crystallineLog p x (kernel_modP p x)) = PeriodRing.pdLog p x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [acrisComparison_eval, WeakAdmissibility.Logarithm.PeriodRings.crystallineLog_mod,
    Nontriviality.pPowerMapBetween_mk, PeriodRing.pdLog_eval]
  have hs : WeakAdmissibilityBridge.uncompletedEquiv p
      (∑ k ∈ Finset.range (p * n),
        WeakAdmissibility.Logarithm.PeriodRings.crystallineLogTerm p x (kernel_modP p x) k) =
      PeriodRing.logPartialSum p x n := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun k _ => uncompletedEquiv_logTerm p x k)
  exact congrArg (Ideal.Quotient.mk ((Ideal.span {(p : PeriodRing.AcrisZero p)}) ^ n)) hs

def powerKernelElement (x : RingHom.ker (PeriodRing.theta p)) (n : ℕ) : RingHom.ker (PeriodRing.theta p) :=
  ⟨(1 + (x : PeriodRing.Ainf p)) ^ n - 1, by
    rw [RingHom.mem_ker, map_sub, map_pow, map_add, map_one,
      RingHom.mem_ker.mp x.property, add_zero, one_pow, sub_self]⟩

/-- The power identity for PeriodInvariants's actual convergent logarithm. -/
theorem pdLog_power (x : RingHom.ker (PeriodRing.theta p)) (n : ℕ) :
    PeriodRing.pdLog p (powerKernelElement p x n) = (n : PeriodRing.Acris p) * PeriodRing.pdLog p x := by
  exact ringEquiv_transport_nat_mul (acrisComparison p)
    (WeakAdmissibility.Logarithm.PeriodRings.crystallineLog p (powerKernelElement p x n)
      (kernel_modP p (powerKernelElement p x n)))
    (WeakAdmissibility.Logarithm.PeriodRings.crystallineLog p x (kernel_modP p x))
    (PeriodRing.pdLog p (powerKernelElement p x n)) (PeriodRing.pdLog p x) n
    (acrisComparison_log p (powerKernelElement p x n)) (acrisComparison_log p x)
    (WeakAdmissibility.Logarithm.crystallineLog_power p x (kernel_modP p x) n)

theorem crystallineLog_congr {x y : PeriodRing.Ainf p} (h : x = y)
    (hx : WeakAdmissibility.Logarithm.PeriodRings.thetaModP p x = 0) (hy : WeakAdmissibility.Logarithm.PeriodRings.thetaModP p y = 0) :
    WeakAdmissibility.Logarithm.PeriodRings.crystallineLog p x hx = WeakAdmissibility.Logarithm.PeriodRings.crystallineLog p y hy := by
  subst y
  rfl

theorem frobenius_pdLog (x y : RingHom.ker (PeriodRing.theta p))
    (hxy : AdicEstimates.Frobenius.ainfFrobenius p x = (y : PeriodRing.Ainf p)) :
    AdicEstimates.Frobenius.acrisFrobenius p (PeriodRing.pdLog p x) = PeriodRing.pdLog p y := by
  have h : WeakAdmissibility.Logarithm.PeriodRings.aInfFrobenius p x = (y : PeriodRing.Ainf p) :=
    (congrArg (fun f : PeriodRing.Ainf p ≃+* PeriodRing.Ainf p => f x)
      (WeakAdmissibilityBridge.ainfFrobenius_eq p)).trans hxy
  calc
    AdicEstimates.Frobenius.acrisFrobenius p (PeriodRing.pdLog p x) = AdicEstimates.Frobenius.acrisFrobenius p
        (acrisComparison p
          (WeakAdmissibility.Logarithm.PeriodRings.crystallineLog p x (kernel_modP p x))) :=
      congrArg (AdicEstimates.Frobenius.acrisFrobenius p) (acrisComparison_log p x).symm
    _ = acrisComparison p
        (WeakAdmissibility.Logarithm.PeriodRings.aCrisFrobenius p
          (WeakAdmissibility.Logarithm.PeriodRings.crystallineLog p x (kernel_modP p x))) :=
      (acrisComparison_frobenius p _).symm
    _ = acrisComparison p
        (WeakAdmissibility.Logarithm.PeriodRings.crystallineLog p (WeakAdmissibility.Logarithm.PeriodRings.aInfFrobenius p x)
          (WeakAdmissibility.Logarithm.PeriodRings.frobenius_kernel p x (kernel_modP p x))) :=
      congrArg (α := WeakAdmissibility.Logarithm.PeriodRings.ACris p) (β := PeriodRing.Acris p) (acrisComparison p)
        (WeakAdmissibility.Logarithm.PeriodRings.frobenius_crystallineLog p x (kernel_modP p x))
    _ = acrisComparison p
        (WeakAdmissibility.Logarithm.PeriodRings.crystallineLog p y (kernel_modP p y)) :=
      congrArg (α := WeakAdmissibility.Logarithm.PeriodRings.ACris p) (β := PeriodRing.Acris p) (acrisComparison p)
        (crystallineLog_congr p h _ (kernel_modP p y))
    _ = PeriodRing.pdLog p y := acrisComparison_log p y

theorem frobenius_cyclotomicKernelElement :
    AdicEstimates.Frobenius.ainfFrobenius p (PeriodRing.cyclotomicKernelElement p) =
      (powerKernelElement p (PeriodRing.cyclotomicKernelElement p) p : PeriodRing.Ainf p) := by
  change AdicEstimates.Frobenius.ainfFrobenius p (WittVector.teichmuller p (PeriodRing.epsilon p) - 1) =
    (1 + (WittVector.teichmuller p (PeriodRing.epsilon p) - 1)) ^ p - 1
  rw [map_sub, map_one]
  change WittVector.frobenius (WittVector.teichmuller p (PeriodRing.epsilon p)) - 1 = _
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
    frobenius_def, map_pow]
  congr 2
  simp

/-- Frobenius acts on the chosen PeriodInvariants cyclotomic period by multiplication by p. -/
theorem frobenius_t : AdicEstimates.Frobenius.acrisFrobenius p (PeriodRing.t p) = (p : PeriodRing.Acris p) * PeriodRing.t p := by
  exact (frobenius_pdLog p (PeriodRing.cyclotomicKernelElement p)
    (powerKernelElement p (PeriodRing.cyclotomicKernelElement p) p)
    (frobenius_cyclotomicKernelElement p)).trans
      (pdLog_power p (PeriodRing.cyclotomicKernelElement p) p)

theorem bcrisPlusFrobenius_t :
    AdicEstimates.Frobenius.bcrisPlusFrobenius p (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p)) =
      (p : PeriodRing.BcrisPlus p) * algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p) := by
  rw [AdicEstimates.Frobenius.bcrisPlusFrobenius_algebraMap, frobenius_t, map_mul, map_natCast]

theorem frobenius_t_isUnit :
    IsUnit (((algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p)).comp (AdicEstimates.Frobenius.bcrisPlusFrobenius p))
      (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p))) := by
  rw [RingHom.comp_apply, bcrisPlusFrobenius_t, map_mul, map_natCast]
  exact (PeriodRing.p_isUnit_bcris p).mul (PeriodRing.t_isUnit_bcris p)

/-- Frobenius extends through inversion of the actual cyclotomic period. -/
def bcrisFrobenius : PeriodRing.Bcris p →+* PeriodRing.Bcris p :=
  Localization.awayLift
    ((algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p)).comp (AdicEstimates.Frobenius.bcrisPlusFrobenius p))
    (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p)) (frobenius_t_isUnit p)

@[simp]
theorem bcrisFrobenius_algebraMap (x : PeriodRing.BcrisPlus p) :
    bcrisFrobenius p (algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) x) =
      algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) (AdicEstimates.Frobenius.bcrisPlusFrobenius p x) :=
  IsLocalization.Away.lift_eq _ (frobenius_t_isUnit p) x

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.Cyclotomic
