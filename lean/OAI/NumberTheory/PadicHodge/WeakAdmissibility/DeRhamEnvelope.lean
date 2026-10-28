import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham
import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicEstimates

/-! # De Rham Envelope -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEnvelope

noncomputable section

/-!
The map from the concrete uncompleted crystalline envelope to B_dR^+.
Extension through p-adic completion is not assumed here.
-/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham
variable (p : ℕ) [Fact p.Prime]

theorem uncompletedEnvelope_eq : Logarithm.PeriodRings.aCrisUncompleted p = PeriodInvariants.PeriodRing.acrisZeroSubalgebra p := by
  calc
    Logarithm.PeriodRings.aCrisUncompleted p = PeriodInvariants.AdicEstimates.Frobenius.modPEnvelope p := by
      unfold Logarithm.PeriodRings.aCrisUncompleted PeriodInvariants.AdicEstimates.Frobenius.modPEnvelope
      apply congrArg (Algebra.adjoin (Logarithm.PeriodRings.AInf p))
      rfl
    _ = PeriodInvariants.PeriodRing.acrisZeroSubalgebra p := PeriodInvariants.AdicEstimates.Frobenius.modPEnvelope_eq_acrisZero p

theorem uncompleted_le_bInf_range :
    Logarithm.PeriodRings.aCrisUncompleted p ≤ (PeriodInvariants.Nontriviality.binfToFractionAlg p).range := by
  rw [uncompletedEnvelope_eq]
  exact PeriodInvariants.Nontriviality.acrisZero_le_binf_range p

def uncompletedLift (x : Logarithm.PeriodRings.ACrisUncompleted p) : Logarithm.PeriodRings.BInf p :=
  (uncompleted_le_bInf_range p x.property).choose

theorem uncompletedLift_spec (x : Logarithm.PeriodRings.ACrisUncompleted p) :
    PeriodInvariants.Nontriviality.binfToFraction p (uncompletedLift p x) =
      (x : Logarithm.PeriodRings.AInfFractionField p) :=
  (uncompleted_le_bInf_range p x.property).choose_spec

/-- The uniquely determined inclusion into A_inf[1/p]. -/
def uncompletedToBInf : Logarithm.PeriodRings.ACrisUncompleted p →+* Logarithm.PeriodRings.BInf p where
  toFun := uncompletedLift p
  map_zero' := (PeriodInvariants.Nontriviality.binfToFraction_injective p) (by
    rw [uncompletedLift_spec, map_zero]
    rfl)
  map_one' := (PeriodInvariants.Nontriviality.binfToFraction_injective p) (by
    rw [uncompletedLift_spec, map_one]
    rfl)
  map_add' x y := (PeriodInvariants.Nontriviality.binfToFraction_injective p) (by
    rw [uncompletedLift_spec, map_add, uncompletedLift_spec, uncompletedLift_spec]
    rfl)
  map_mul' x y := (PeriodInvariants.Nontriviality.binfToFraction_injective p) (by
    rw [uncompletedLift_spec, map_mul, uncompletedLift_spec, uncompletedLift_spec]
    rfl)

theorem uncompletedToBInf_fraction (x : Logarithm.PeriodRings.ACrisUncompleted p) :
    PeriodInvariants.Nontriviality.binfToFraction p (uncompletedToBInf p x) =
      (x : Logarithm.PeriodRings.AInfFractionField p) := uncompletedLift_spec p x

theorem uncompletedToBInf_injective : Function.Injective (uncompletedToBInf p) := by
  intro x y h
  apply Subtype.ext
  have he := congrArg (PeriodInvariants.Nontriviality.binfToFraction p) h
  simpa only [uncompletedToBInf_fraction] using he

theorem uncompletedToBInf_algebraMap (x : Logarithm.PeriodRings.AInf p) :
    uncompletedToBInf p (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) x) =
      algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) x := by
  apply PeriodInvariants.Nontriviality.binfToFraction_injective p
  rw [uncompletedToBInf_fraction, PeriodInvariants.Nontriviality.binfToFraction_algebraMap]
  rfl

def uncompletedToBdRPlus : Logarithm.PeriodRings.ACrisUncompleted p →+* Logarithm.PeriodRings.BdRPlus p :=
  (DeRham.bInfToBdRPlus p).comp (uncompletedToBInf p)

theorem uncompletedToBdRPlus_algebraMap (x : Logarithm.PeriodRings.AInf p) :
    uncompletedToBdRPlus p (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) x) =
      DeRham.bInfToBdRPlus p (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) x) := by
  rw [uncompletedToBdRPlus, RingHom.comp_apply, uncompletedToBInf_algebraMap]

theorem uncompleted_kernel_mem_filtration (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.theta p x = 0) :
    uncompletedToBdRPlus p (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) x) ∈
      DeRham.positiveFiltration p 1 := by
  rw [DeRham.positiveFiltration, pow_one, RingHom.mem_ker, uncompletedToBdRPlus_algebraMap,
    DeRham.thetaBdRPlus_aInf, hx, map_zero]

theorem factorial_isUnit_bdRPlus (n : ℕ) : IsUnit (n.factorial : Logarithm.PeriodRings.BdRPlus p) := by
  have hu : IsUnit (n.factorial : ℚ_[p]) :=
    isUnit_iff_ne_zero.mpr (by exact_mod_cast Nat.factorial_ne_zero n)
  simpa only [map_natCast] using hu.map
    ((DeRham.bInfToBdRPlus p).comp (PeriodInvariants.Nontriviality.padicToBinf p))

theorem factorial_mul_dividedPower (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.thetaModP p x = 0) (n : ℕ) :
    (n.factorial : Logarithm.PeriodRings.ACrisUncompleted p) * Logarithm.PeriodRings.dividedPower p x n hx =
      algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) x ^ n := by
  apply Subtype.ext
  change (n.factorial : Logarithm.PeriodRings.AInfFractionField p) *
    (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) x ^ n / (n.factorial : Logarithm.PeriodRings.AInfFractionField p)) =
      algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) x ^ n
  have hn : (n.factorial : Logarithm.PeriodRings.AInfFractionField p) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp

/-- Divided powers of the theta kernel have the expected de Rham filtration degree. -/
theorem dividedPower_mem_filtration (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.theta p x = 0) (n : ℕ)
    (hxmod : Logarithm.PeriodRings.thetaModP p x = 0) :
    uncompletedToBdRPlus p (Logarithm.PeriodRings.dividedPower p x n hxmod) ∈ DeRham.positiveFiltration p n := by
  have hker : uncompletedToBdRPlus p (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) x) ∈
      RingHom.ker (DeRham.thetaBdRPlus p) := by
    simpa only [DeRham.positiveFiltration, pow_one] using uncompleted_kernel_mem_filtration p x hx
  have hpow := Ideal.pow_mem_pow hker n
  rw [← map_pow, ← factorial_mul_dividedPower p x hxmod n, map_mul, map_natCast] at hpow
  exact (Submodule.smul_mem_iff_of_isUnit _ (factorial_isUnit_bdRPlus p n)).mp hpow

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEnvelope
