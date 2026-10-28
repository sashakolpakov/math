import OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing

/-! # Nontriviality -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality

noncomputable section

/-!
# Nontriviality of the concrete PeriodInvariants period rings

We first construct theta on the divided-power envelope and its completion.
This uses the actual localization of `A_inf`, rather than postulating a
comparison map or a nonzero period ring.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing

variable (p : ℕ) [hp : Fact p.Prime]

abbrev Binf : Type := Localization.Away (p : PeriodRing.Ainf p)

theorem p_isUnit_binf : IsUnit (p : Binf p) := by
  simpa only [map_natCast] using
    (IsLocalization.Away.algebraMap_isUnit (R := PeriodRing.Ainf p) (S := Binf p) p)

def binfToFraction : Binf p →+* FractionRing (PeriodRing.Ainf p) :=
  IsLocalization.Away.lift (p : PeriodRing.Ainf p)
    (g := algebraMap (PeriodRing.Ainf p) (FractionRing (PeriodRing.Ainf p)))
    (by
      apply isUnit_iff_ne_zero.mpr
      simpa only [map_natCast] using
        (show (p : FractionRing (PeriodRing.Ainf p)) ≠ 0 by exact_mod_cast hp.out.ne_zero))

@[simp]
theorem binfToFraction_algebraMap (x : PeriodRing.Ainf p) :
    binfToFraction p (algebraMap (PeriodRing.Ainf p) (Binf p) x) =
      algebraMap (PeriodRing.Ainf p) (FractionRing (PeriodRing.Ainf p)) x :=
  IsLocalization.Away.lift_eq _ _ x

def binfToFractionAlg : Binf p →ₐ[PeriodRing.Ainf p] FractionRing (PeriodRing.Ainf p) :=
  { binfToFraction p with commutes' := binfToFraction_algebraMap p }

theorem binf_algebraMap_injective :
    Function.Injective (algebraMap (PeriodRing.Ainf p) (Binf p)) :=
  IsLocalization.injective (Binf p)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (show (p : PeriodRing.Ainf p) ≠ 0 by exact_mod_cast hp.out.ne_zero))

theorem binfToFraction_injective : Function.Injective (binfToFraction p) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (M := Submonoid.powers (p : PeriodRing.Ainf p)) (binfToFraction p)).mpr
  intro x y
  simp only [binfToFraction_algebraMap, (binf_algebraMap_injective p).eq_iff,
    (IsFractionRing.injective (PeriodRing.Ainf p) (FractionRing (PeriodRing.Ainf p))).eq_iff]

/-- Theta extends to the localization because `p` is nonzero in `ℂ_p`. -/
def binfTheta : Binf p →+* ℂ_[p] :=
  IsLocalization.Away.lift (p : PeriodRing.Ainf p)
    (g := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (PeriodRing.theta p))
    (by
      apply isUnit_iff_ne_zero.mpr
      simpa only [map_natCast] using
        (show (p : ℂ_[p]) ≠ 0 by exact_mod_cast hp.out.ne_zero))

@[simp]
theorem binfTheta_algebraMap (x : PeriodRing.Ainf p) :
    binfTheta p (algebraMap (PeriodRing.Ainf p) (Binf p) x) =
      algebraMap 𝓞_ℂ_[p] ℂ_[p] (PeriodRing.theta p x) :=
  IsLocalization.Away.lift_eq _ _ x

def padicIntToBinf : ℤ_[p] →+* Binf p :=
  (algebraMap (PeriodRing.Ainf p) (Binf p)).comp (PeriodRing.padicIntToAinf p)

def padicToBinf : ℚ_[p] →+* Binf p :=
  IsLocalization.lift (S := ℚ_[p]) (g := padicIntToBinf p)
    (fun y : nonZeroDivisors ℤ_[p] => PeriodRing.padicInt_map_nonzero_isUnit p
      (padicIntToBinf p) (by simpa only [map_natCast] using p_isUnit_binf p)
      (mem_nonZeroDivisors_iff_ne_zero.mp y.property))

/-- The factorial denominators in the crystalline envelope already exist in
`A_inf[1/p]`, through its constructed `ℚ_p` constants. -/
def binfDividedPower (n : ℕ) (x : RingHom.ker (PeriodRing.theta p)) : Binf p :=
  (algebraMap (PeriodRing.Ainf p) (Binf p) (x : PeriodRing.Ainf p)) ^ n *
    padicToBinf p ((n.factorial : ℚ_[p])⁻¹)

theorem binfDividedPower_fraction (n : ℕ) (x : RingHom.ker (PeriodRing.theta p)) :
    binfToFraction p (binfDividedPower p n x) =
      (PeriodRing.dividedPower p n x : FractionRing (PeriodRing.Ainf p)) := by
  rw [binfDividedPower, map_mul, map_pow, binfToFraction_algebraMap, PeriodRing.dividedPower_coe]
  have hd : binfToFraction p (padicToBinf p ((n.factorial : ℚ_[p])⁻¹)) =
      (n.factorial : FractionRing (PeriodRing.Ainf p))⁻¹ := by
    change ((binfToFraction p).comp (padicToBinf p)) ((n.factorial : ℚ_[p])⁻¹) = _
    rw [map_inv₀, map_natCast]
  rw [hd, div_eq_mul_inv]

@[simp]
theorem binfDividedPower_zero (x : RingHom.ker (PeriodRing.theta p)) :
    binfDividedPower p 0 x = 1 := by
  simp [binfDividedPower]

theorem binfTheta_dividedPower_succ (n : ℕ) (x : RingHom.ker (PeriodRing.theta p)) :
    binfTheta p (binfDividedPower p (n + 1) x) = 0 := by
  rw [binfDividedPower, map_mul, map_pow, binfTheta_algebraMap,
    RingHom.mem_ker.mp x.property, map_zero]
  simp

/-- The concrete envelope lies in the rational Fontaine ring. -/
theorem acrisZero_le_binf_range : PeriodRing.acrisZeroSubalgebra p ≤ (binfToFractionAlg p).range := by
  apply Algebra.adjoin_le
  rintro _ ⟨⟨n, x⟩, rfl⟩
  exact ⟨binfDividedPower p n x, binfDividedPower_fraction p n x⟩

def acrisZeroLift (x : PeriodRing.AcrisZero p) : Binf p :=
  (acrisZero_le_binf_range p x.property).choose

@[simp]
theorem acrisZeroLift_spec (x : PeriodRing.AcrisZero p) :
    binfToFraction p (acrisZeroLift p x) = (x : FractionRing (PeriodRing.Ainf p)) :=
  (acrisZero_le_binf_range p x.property).choose_spec

/-- The uniquely determined inclusion of the concrete envelope into
`A_inf[1/p]`; ring laws follow from the proved injection into the fraction field. -/
def acrisZeroToBinf : PeriodRing.AcrisZero p →+* Binf p where
  toFun := acrisZeroLift p
  map_zero' := (binfToFraction_injective p) (by simp)
  map_one' := (binfToFraction_injective p) (by simp)
  map_add' x y := (binfToFraction_injective p) (by simp)
  map_mul' x y := (binfToFraction_injective p) (by simp)

@[simp]
theorem acrisZeroToBinf_algebraMap (x : PeriodRing.Ainf p) :
    acrisZeroToBinf p (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) x) =
      algebraMap (PeriodRing.Ainf p) (Binf p) x := by
  apply binfToFraction_injective p
  change binfToFraction p (acrisZeroLift p _) = _
  rw [acrisZeroLift_spec, binfToFraction_algebraMap]
  rfl

@[simp]
theorem acrisZeroToBinf_dividedPower (n : ℕ) (x : RingHom.ker (PeriodRing.theta p)) :
    acrisZeroToBinf p (PeriodRing.dividedPower p n x) = binfDividedPower p n x := by
  apply binfToFraction_injective p
  exact (acrisZeroLift_spec p _).trans (binfDividedPower_fraction p n x).symm

def thetaZeroField : PeriodRing.AcrisZero p →+* ℂ_[p] :=
  (binfTheta p).comp (acrisZeroToBinf p)

@[simp]
theorem thetaZeroField_algebraMap (x : PeriodRing.Ainf p) :
    thetaZeroField p (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) x) =
      algebraMap 𝓞_ℂ_[p] ℂ_[p] (PeriodRing.theta p x) := by
  simp [thetaZeroField]

theorem thetaZeroField_dividedPower_succ (n : ℕ) (x : RingHom.ker (PeriodRing.theta p)) :
    thetaZeroField p (PeriodRing.dividedPower p (n + 1) x) = 0 := by
  simp only [thetaZeroField, RingHom.comp_apply, acrisZeroToBinf_dividedPower,
    binfTheta_dividedPower_succ]

/-- All elements of the integral envelope have integral theta values. -/
theorem thetaZeroField_integral (x : PeriodRing.AcrisZero p) :
    thetaZeroField p x ∈ 𝓞_ℂ_[p] := by
  obtain ⟨x, hx⟩ := x
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
      obtain ⟨⟨n, z⟩, rfl⟩ := hy
      change thetaZeroField p (PeriodRing.dividedPower p n z) ∈ 𝓞_ℂ_[p]
      cases n with
      | zero => simp
      | succ n => rw [thetaZeroField_dividedPower_succ]; exact (PadicComplexInt p).zero_mem
  | algebraMap a =>
      change thetaZeroField p (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) a) ∈ 𝓞_ℂ_[p]
      rw [thetaZeroField_algebraMap]
      exact (PeriodRing.theta p a).property
  | add x y hx hy ihx ihy =>
      change thetaZeroField p ((⟨x, hx⟩ : PeriodRing.AcrisZero p) + (⟨y, hy⟩ : PeriodRing.AcrisZero p)) ∈ _
      rw [(thetaZeroField p).map_add]
      exact (PadicComplexInt p).add_mem _ _ ihx ihy
  | mul x y hx hy ihx ihy =>
      change thetaZeroField p ((⟨x, hx⟩ : PeriodRing.AcrisZero p) * (⟨y, hy⟩ : PeriodRing.AcrisZero p)) ∈ _
      rw [(thetaZeroField p).map_mul]
      exact (PadicComplexInt p).mul_mem _ _ ihx ihy

/-- Fontaine theta on the uncompleted divided-power envelope, with its
integral target established by the preceding proof. -/
def thetaZero : PeriodRing.AcrisZero p →+* 𝓞_ℂ_[p] where
  toFun x := ⟨thetaZeroField p x, thetaZeroField_integral p x⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext ((thetaZeroField p).map_add x y)
  map_mul' x y := Subtype.ext ((thetaZeroField p).map_mul x y)

@[simp]
theorem thetaZero_algebraMap (x : PeriodRing.Ainf p) :
    thetaZero p (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) x) = PeriodRing.theta p x :=
  Subtype.ext (thetaZeroField_algebraMap p x)

theorem thetaZero_surjective : Function.Surjective (thetaZero p) := by
  intro x
  obtain ⟨a, ha⟩ := PeriodRing.theta_surjective p x
  exact ⟨algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) a, (thetaZero_algebraMap p a).trans ha⟩

section CompletionLift

omit hp
variable {S T : Type*} [CommRing S] [CommRing T]

def pPowerMapBetween (f : S →+* T) (n : ℕ) :
    S ⧸ (Ideal.span {(p : S)}) ^ n →+* T ⧸ (Ideal.span {(p : T)}) ^ n :=
  Ideal.quotientMap _ f (by
    rw [← Ideal.map_le_iff_le_comap]
    simp only [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]
    exact le_rfl)

@[simp]
theorem pPowerMapBetween_mk (f : S →+* T) (n : ℕ) (x : S) :
    pPowerMapBetween p f n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (f x) := rfl

theorem pPowerMapBetween_factorPow (f : S →+* T) {m n : ℕ} (h : m ≤ n)
    (x : S ⧸ (Ideal.span {(p : S)}) ^ n) :
    Ideal.Quotient.factorPow (Ideal.span {(p : T)}) h (pPowerMapBetween p f n x) =
      pPowerMapBetween p f m (Ideal.Quotient.factorPow (Ideal.span {(p : S)}) h x) := by
  induction x using Quotient.inductionOn' with
  | h x => rfl

def completionLiftComponent (f : S →+* T) (n : ℕ) :
    AdicCompletion (Ideal.span {(p : S)}) S →+* T ⧸ (Ideal.span {(p : T)}) ^ n :=
  (pPowerMapBetween p f n).comp (AdicCompletion.evalₐ (Ideal.span {(p : S)}) n).toRingHom

theorem completionLiftComponent_compatible (f : S →+* T) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : T)}) h).comp
        (completionLiftComponent p f n) = completionLiftComponent p f m := by
  apply RingHom.ext
  intro x
  change Ideal.Quotient.factorPow _ h
      (pPowerMapBetween p f n (AdicCompletion.evalₐ _ n x)) =
    pPowerMapBetween p f m (AdicCompletion.evalₐ _ m x)
  rw [pPowerMapBetween_factorPow, PeriodRing.completionEval_factorPow]

variable [IsAdicComplete (Ideal.span {(p : T)}) T]

/-- Extend a ring map into a `p`-adically complete target, by compatible
quotients. No continuity assumption is needed: ring maps preserve `(p)^n`. -/
def completionLift (f : S →+* T) : AdicCompletion (Ideal.span {(p : S)}) S →+* T :=
  IsAdicComplete.liftRingHom (Ideal.span {(p : T)}) (completionLiftComponent p f)
    (completionLiftComponent_compatible p f)

theorem completionLift_mod (f : S →+* T) (n : ℕ)
    (x : AdicCompletion (Ideal.span {(p : S)}) S) :
    Ideal.Quotient.mk ((Ideal.span {(p : T)}) ^ n) (completionLift p f x) =
      completionLiftComponent p f n x :=
  IsAdicComplete.mk_liftRingHom (Ideal.span {(p : T)}) (completionLiftComponent p f)
    (completionLiftComponent_compatible p f) n x

@[simp]
theorem completionLift_of (f : S →+* T) (x : S) :
    completionLift p f (AdicCompletion.of (Ideal.span {(p : S)}) S x) = f x := by
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : T)})]
  simp only [smul_eq_mul, Ideal.mul_top]
  intro n
  have h := completionLift_mod p f n (AdicCompletion.of (Ideal.span {(p : S)}) S x)
  have heval : completionLiftComponent p f n
      (AdicCompletion.of (Ideal.span {(p : S)}) S x) =
        Ideal.Quotient.mk ((Ideal.span {(p : T)}) ^ n) (f x) := by
    change pPowerMapBetween p f n
      (AdicCompletion.evalₐ _ n (AdicCompletion.of _ S x)) = _
    rw [AdicCompletion.evalₐ_of, pPowerMapBetween_mk]
  rw [heval] at h
  simpa only [SModEq.idealQuotientMk] using h

end CompletionLift

/-- The actual theta map on `A_cris`. -/
def thetaAcris : PeriodRing.Acris p →+* 𝓞_ℂ_[p] := completionLift p (thetaZero p)

@[simp]
theorem thetaAcris_algebraMap (x : PeriodRing.AcrisZero p) :
    thetaAcris p (algebraMap (PeriodRing.AcrisZero p) (PeriodRing.Acris p) x) = thetaZero p x :=
  completionLift_of p (thetaZero p) x

theorem thetaAcris_surjective : Function.Surjective (thetaAcris p) := by
  intro x
  obtain ⟨a, ha⟩ := thetaZero_surjective p x
  exact ⟨algebraMap (PeriodRing.AcrisZero p) (PeriodRing.Acris p) a, (thetaAcris_algebraMap p a).trans ha⟩

instance acris_charZero : CharZero (PeriodRing.Acris p) where
  cast_injective m n h := by
    apply Nat.cast_injective (R := 𝓞_ℂ_[p])
    simpa only [map_natCast] using congrArg (thetaAcris p) h

instance acris_nontrivial : Nontrivial (PeriodRing.Acris p) := inferInstance

/-- The completed theta map extends to `B_cris⁺` with values in `ℂ_p`. -/
def thetaBcrisPlus : PeriodRing.BcrisPlus p →+* ℂ_[p] :=
  IsLocalization.Away.lift (p : PeriodRing.Acris p)
    (g := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (thetaAcris p))
    (by
      apply isUnit_iff_ne_zero.mpr
      simpa only [map_natCast] using
        (show (p : ℂ_[p]) ≠ 0 by exact_mod_cast hp.out.ne_zero))

@[simp]
theorem thetaBcrisPlus_algebraMap (x : PeriodRing.Acris p) :
    thetaBcrisPlus p (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) x) =
      algebraMap 𝓞_ℂ_[p] ℂ_[p] (thetaAcris p x) :=
  IsLocalization.Away.lift_eq _ _ x

instance bcrisPlus_charZero : CharZero (PeriodRing.BcrisPlus p) where
  cast_injective m n h := by
    apply Nat.cast_injective (R := ℂ_[p])
    simpa only [map_natCast] using congrArg (thetaBcrisPlus p) h

instance bcrisPlus_nontrivial : Nontrivial (PeriodRing.BcrisPlus p) := inferInstance

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality
