import OAI.NumberTheory.PadicHodge.PeriodInvariants.Galois
import OAI.NumberTheory.PadicHodge.PeriodInvariants.Logarithm

/-! # Tate Cyclotomic -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.Roots

/-!
# Compatible roots of unity and their crystalline logarithms

The group consists of actual compatible sequences in the ring of integers,
with zeroth coefficient one. Its logarithm is the constructed divided-power
logarithm in A_cris.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.Galois OAI.NumberTheory.PadicHodge.PeriodInvariants.Cyclotomic OAI.NumberTheory.PadicHodge.PeriodInvariants.Logarithm

section PerfectionUnits

variable (p : ℕ) {M : Type*} [CommMonoid M]

def perfectionUnit (x : Perfection M p)
    (hx : ∀ n, IsUnit (Perfection.coeffMonoidHom M p n x)) : (Perfection M p)ˣ where
  val := x
  inv := ⟨fun n => ↑((hx n).unit⁻¹), fun n => by
    have h : (hx (n + 1)).unit ^ p = (hx n).unit := by
      apply Units.ext
      exact x.property n
    rw [← Units.val_pow_eq_pow_val, inv_pow, h]⟩
  val_inv := by
    apply Perfection.extMonoid
    intro n
    exact (hx n).mul_val_inv
  inv_val := by
    apply Perfection.extMonoid
    intro n
    exact (hx n).val_inv_mul

def rootShift : ℕ → Perfection M p →* Perfection M p
  | 0 => MonoidHom.id _
  | n + 1 => (Perfection.pthRootMonoidHom M p).comp (rootShift n)

theorem rootShift_coeff (n k : ℕ) (x : Perfection M p) :
    Perfection.coeffMonoidHom M p k (Roots.rootShift p n x) =
      Perfection.coeffMonoidHom M p (k + n) x := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      change Perfection.coeffMonoidHom M p (k + 1) (Roots.rootShift p n x) = _
      rw [ih]
      exact congrArg (fun j : ℕ => Perfection.coeffMonoidHom M p j x) (by omega)

theorem rootShift_pow (n : ℕ) (x : Perfection M p) : Roots.rootShift p n x ^ p ^ n = x := by
  apply Perfection.extMonoid
  intro k
  rw [map_pow, rootShift_coeff, Perfection.coeffMonoidHom_pow_p_pow']

end PerfectionUnits

variable (p : ℕ) [Fact p.Prime]

def rootTowerGroup : Subgroup (Perfection 𝓞_ℂ_[p] p)ˣ :=
  (Units.map (Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0)).ker

abbrev RootTower := rootTowerGroup p

def rootValue (x : RootTower p) : Perfection 𝓞_ℂ_[p] p := x.val.val

theorem rootValue_zero (x : RootTower p) :
    Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 (rootValue p x) = 1 :=
  congrArg Units.val x.property

def rootTowerOfSequence (x : Perfection 𝓞_ℂ_[p] p)
    (hx : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 x = 1) : RootTower p :=
  ⟨perfectionUnit p x (fun n => IsUnit.of_pow_eq_one
    ((Perfection.coeffMonoidHom_pow_p_pow_self x n).trans hx)
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero)), by
      apply Units.ext
      exact hx⟩

def rootTilt (x : RootTower p) : PreTilt 𝓞_ℂ_[p] p := PeriodRing.tiltMonoidEquiv p (rootValue p x)

theorem rootTilt_untilt (x : RootTower p) : (rootTilt p x).untilt = 1 :=
  (PeriodRing.untilt_tiltMonoidEquiv p (rootValue p x)).trans (rootValue_zero p x)

def rootKernelElement (x : RootTower p) : RingHom.ker (PeriodRing.theta p) :=
  ⟨WittVector.teichmuller p (rootTilt p x) - 1, by
    rw [RingHom.mem_ker, map_sub, PeriodRing.theta_teichmuller, map_one, rootTilt_untilt, sub_self]⟩

def rootLog (x : RootTower p) : PeriodRing.Acris p := PeriodRing.pdLog p (rootKernelElement p x)

theorem rootKernelElement_mul (x y : RootTower p) :
    rootKernelElement p (x * y) =
      Logarithm.productKernelElement p (rootKernelElement p x) (rootKernelElement p y) := by
  apply Subtype.val_injective
  have ht : rootTilt p (x * y) = rootTilt p x * rootTilt p y :=
    map_mul (PeriodRing.tiltMonoidEquiv p) (rootValue p x) (rootValue p y)
  change WittVector.teichmuller p (rootTilt p (x * y)) - 1 =
    (WittVector.teichmuller p (rootTilt p x) - 1) +
      (WittVector.teichmuller p (rootTilt p y) - 1) +
      (WittVector.teichmuller p (rootTilt p x) - 1) *
        (WittVector.teichmuller p (rootTilt p y) - 1)
  rw [ht, map_mul]
  ring

theorem rootLog_mul (x y : RootTower p) : rootLog p (x * y) = rootLog p x + rootLog p y := by
  rw [rootLog, rootKernelElement_mul, Logarithm.pdLog_product]
  rfl

theorem rootLog_one : rootLog p 1 = 0 := by
  have h := rootLog_mul p 1 1
  have h' : rootLog p 1 + 0 = rootLog p 1 + rootLog p 1 := by
    simpa only [one_mul, add_zero] using h
  exact (add_left_cancel h').symm

def rootLogHom : RootTower p →* Multiplicative (PeriodRing.Acris p) where
  toFun x := Multiplicative.ofAdd (rootLog p x)
  map_one' := rootLog_one p
  map_mul' := rootLog_mul p

theorem rootLog_pow (x : RootTower p) (n : ℕ) : rootLog p (x ^ n) = (n : PeriodRing.Acris p) * rootLog p x := by
  induction n with
  | zero => simp only [pow_zero, rootLog_one, Nat.cast_zero, zero_mul]
  | succ n ih =>
      rw [pow_succ, rootLog_mul, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

theorem rootLog_inv (x : RootTower p) : rootLog p x⁻¹ = -rootLog p x := by
  have h := rootLog_mul p x x⁻¹
  rw [mul_inv_cancel, rootLog_one] at h
  apply eq_neg_iff_add_eq_zero.mpr
  rw [add_comm]
  exact h.symm

theorem rootRatio_coeff (x y : RootTower p) (n : ℕ)
    (hxy : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (rootValue p x) =
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (rootValue p y)) :
    Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (rootValue p (x * y⁻¹)) = 1 := by
  have hu : Units.map (Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n) x.val =
      Units.map (Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n) y.val := Units.ext hxy
  have h : Units.map (Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n) (x.val * y.val⁻¹) = 1 := by
    rw [map_mul, map_inv, hu, mul_inv_cancel]
  exact congrArg Units.val h

/-- If two root towers agree in degree n, their ratio has a p^n-th root
whose zeroth coefficient is one. -/
def rootDifferenceRoot (x y : RootTower p) (n : ℕ)
    (hxy : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (rootValue p x) =
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (rootValue p y)) : RootTower p :=
  ⟨Units.map (Roots.rootShift p n) (x.val * y.val⁻¹), by
    apply Units.ext
    change Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0
      (Roots.rootShift p n (rootValue p (x * y⁻¹))) = 1
    rw [rootShift_coeff, zero_add]
    exact rootRatio_coeff p x y n hxy⟩

theorem rootDifferenceRoot_pow (x y : RootTower p) (n : ℕ)
    (hxy : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (rootValue p x) =
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (rootValue p y)) :
    rootDifferenceRoot p x y n hxy ^ p ^ n = x * y⁻¹ := by
  apply Subtype.val_injective
  apply Units.ext
  exact rootShift_pow p n (rootValue p (x * y⁻¹))

theorem rootLog_difference (x y : RootTower p) (n : ℕ)
    (hxy : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (rootValue p x) =
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (rootValue p y)) :
    rootLog p x - rootLog p y = (p : PeriodRing.Acris p) ^ n * rootLog p (rootDifferenceRoot p x y n hxy) := by
  have h := rootLog_pow p (rootDifferenceRoot p x y n hxy) (p ^ n)
  rw [rootDifferenceRoot_pow, rootLog_mul, rootLog_inv, Nat.cast_pow] at h
  simpa only [sub_eq_add_neg] using h

section AdicEvaluation

omit [Fact p.Prime]
variable {R : Type*} [CommRing R]

theorem adic_eval_p_pow_mul (n : ℕ) (z : AdicCompletion (Ideal.span {(p : R)}) R) :
    AdicCompletion.evalₐ (Ideal.span {(p : R)}) n
      ((p : AdicCompletion (Ideal.span {(p : R)}) R) ^ n * z) = 0 := by
  have hp : (p : R ⧸ (Ideal.span {(p : R)}) ^ n) ^ n = 0 := by
    have hm : (p : R) ^ n ∈ (Ideal.span {(p : R)}) ^ n :=
      Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) n
    simpa only [map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hm
  rw [map_mul, map_pow, map_natCast, hp, zero_mul]

end AdicEvaluation

/-- Agreement of root towers at a finite level gives a congruence of their
actual logarithms at the corresponding p-adic precision. -/
theorem rootLog_congr_eval (x y : RootTower p) (n : ℕ)
    (hxy : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (rootValue p x) =
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (rootValue p y)) :
    AdicCompletion.evalₐ (Ideal.span {(p : PeriodRing.AcrisZero p)}) n (rootLog p x) =
      AdicCompletion.evalₐ (Ideal.span {(p : PeriodRing.AcrisZero p)}) n (rootLog p y) := by
  have h := congrArg (AdicCompletion.evalₐ (Ideal.span {(p : PeriodRing.AcrisZero p)}) n)
    (rootLog_difference p x y n hxy)
  rw [adic_eval_p_pow_mul, map_sub] at h
  exact sub_eq_zero.mp h

def cyclotomicRootTower : RootTower p := rootTowerOfSequence p (PeriodRing.cyclotomicRoots p) rfl

theorem cyclotomicRootTower_log : rootLog p (cyclotomicRootTower p) = PeriodRing.t p := rfl

def rootTowerMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) : RootTower p →* RootTower p where
  toFun x := ⟨Units.map (Perfection.mapMonoidHom p f.toMonoidHom) x.val, by
    apply Units.ext
    change f (Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 (rootValue p x)) = 1
    rw [rootValue_zero, map_one]⟩
  map_one' := Subtype.ext (Units.map (Perfection.mapMonoidHom p f.toMonoidHom)).map_one
  map_mul' x y :=
    Subtype.ext ((Units.map (Perfection.mapMonoidHom p f.toMonoidHom)).map_mul x.val y.val)

theorem rootTilt_map (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (x : RootTower p) :
    PeriodRing.tiltMap p f (rootTilt p x) = rootTilt p (rootTowerMap p f x) :=
  PeriodRing.tiltMap_rootSequence p f (rootValue p x)

theorem rootKernelElement_map (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (x : RootTower p) :
    PeriodRing.thetaKernelMap p f (rootKernelElement p x) = rootKernelElement p (rootTowerMap p f x) := by
  apply Subtype.val_injective
  change PeriodRing.ainfMap p f (WittVector.teichmuller p (rootTilt p x) - 1) =
    WittVector.teichmuller p (rootTilt p (rootTowerMap p f x)) - 1
  rw [map_sub, map_one, PeriodRing.ainfMap_teichmuller, rootTilt_map]

theorem rootLog_natural (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : RootTower p) :
    PeriodRing.acrisEquiv p f (rootLog p x) = rootLog p (rootTowerMap p f.toRingHom x) := by
  change PeriodRing.acrisMap p f (PeriodRing.pdLog p (rootKernelElement p x)) = _
  rw [PeriodRing.acrisMap_pdLog, rootKernelElement_map]
  rfl

def cyclotomicApproximation (σ : PeriodRing.PadicGalois p) (n : ℕ) : ℕ :=
  (((Galois.cyclotomicExponent p σ).val).toZModPow n).val

theorem galois_t_approx_eval (σ : PeriodRing.PadicGalois p) (n : ℕ) :
    AdicCompletion.evalₐ (Ideal.span {(p : PeriodRing.AcrisZero p)}) n
        (PeriodRing.acrisEquiv p (PeriodRing.galoisIntegerEquiv p σ) (PeriodRing.t p)) =
      AdicCompletion.evalₐ (Ideal.span {(p : PeriodRing.AcrisZero p)}) n
        ((cyclotomicApproximation p σ n : PeriodRing.Acris p) * PeriodRing.t p) := by
  have hc : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n
      (rootValue p (rootTowerMap p (PeriodRing.galoisIntegerEquiv p σ).toRingHom (cyclotomicRootTower p))) =
    Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n
      (rootValue p (cyclotomicRootTower p ^ cyclotomicApproximation p σ n)) :=
    Galois.galois_cyclotomicRootSequence p σ n
  have h := rootLog_congr_eval p
    (rootTowerMap p (PeriodRing.galoisIntegerEquiv p σ).toRingHom (cyclotomicRootTower p))
    (cyclotomicRootTower p ^ cyclotomicApproximation p σ n) n hc
  rw [rootLog_pow, cyclotomicRootTower_log, ← rootLog_natural, cyclotomicRootTower_log] at h
  exact h

end NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.Roots

namespace NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.Galois

/-!
# The cyclotomic Galois identity and inversion of the period

The p-adic character is identified by its reductions on actual roots of unity.
The logarithm congruences then prove the identity in the completed ring.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.Galois OAI.NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.Roots OAI.NumberTheory.PadicHodge.PeriodInvariants.Cyclotomic

theorem awayLifts_comp {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S]
    (F G H : S →+* S) (f g h : R →+* R)
    (hF : ∀ x, F (algebraMap R S x) = algebraMap R S (f x))
    (hG : ∀ x, G (algebraMap R S x) = algebraMap R S (g x))
    (hH : ∀ x, H (algebraMap R S x) = algebraMap R S (h x))
    (hfg : ∀ x, h x = f (g x)) : H = F.comp G := by
  apply IsLocalization.ringHom_ext (M := Submonoid.powers r)
  apply RingHom.ext
  intro x
  change H (algebraMap R S x) = F (G (algebraMap R S x))
  rw [hH, hG, hF, hfg]

theorem awayLifts_commute {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S]
    (F G : S →+* S) (f g : R →+* R)
    (hF : ∀ x, F (algebraMap R S x) = algebraMap R S (f x))
    (hG : ∀ x, G (algebraMap R S x) = algebraMap R S (g x))
    (hfg : ∀ x, f (g x) = g (f x)) : F.comp G = G.comp F := by
  apply IsLocalization.ringHom_ext (M := Submonoid.powers r)
  apply RingHom.ext
  intro x
  change F (G (algebraMap R S x)) = G (F (algebraMap R S x))
  rw [hG, hF, hF, hG, hfg]

variable (p : ℕ) [Fact p.Prime]

def padicIntToAcris : ℤ_[p] →+* PeriodRing.Acris p :=
  (algebraMap (PeriodRing.AcrisZero p) (PeriodRing.Acris p)).comp
    ((algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p)).comp (PeriodRing.padicIntToAinf p))

theorem padicIntToAcris_bcrisPlus (a : ℤ_[p]) :
    algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (padicIntToAcris p a) = PeriodRing.padicIntToBcrisPlus p a := rfl

theorem map_padicInt_approx {S : Type*} [CommRing S] (f : ℤ_[p] →+* S)
    (n : ℕ) (hp : (p : S) ^ n = 0) (a : ℤ_[p]) :
    f a = (((a.toZModPow n).val : ℕ) : S) := by
  have hd : (p : ℤ_[p]) ^ n ∣ a - ((a.toZModPow n).val : ℤ_[p]) := by
    apply Ideal.mem_span_singleton.mp
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast]
    simp only [ZMod.natCast_zmod_val, sub_self]
  obtain ⟨b, hb⟩ := hd
  have hz : f (a - ((a.toZModPow n).val : ℤ_[p])) = 0 := by
    rw [hb, map_mul, map_pow, map_natCast, hp, zero_mul]
  simpa only [map_sub, map_natCast, sub_eq_zero] using hz

omit [Fact p.Prime] in
theorem quotient_p_pow_zero {R : Type*} [CommRing R] (n : ℕ) :
    (p : R ⧸ (Ideal.span {(p : R)}) ^ n) ^ n = 0 := by
  have hm : (p : R) ^ n ∈ (Ideal.span {(p : R)}) ^ n :=
    Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) n
  simpa only [map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hm

theorem padicIntToAcris_approx_eval (a : ℤ_[p]) (n : ℕ) :
    AdicCompletion.evalₐ (Ideal.span {(p : PeriodRing.AcrisZero p)}) n (padicIntToAcris p a) =
      (((a.toZModPow n).val : ℕ) : PeriodRing.AcrisZero p ⧸ (Ideal.span {(p : PeriodRing.AcrisZero p)}) ^ n) :=
  map_padicInt_approx p
    ((AdicCompletion.evalₐ (Ideal.span {(p : PeriodRing.AcrisZero p)}) n).toRingHom.comp (padicIntToAcris p))
    n (quotient_p_pow_zero p n) a

theorem map_mul_of_map_eq {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b c : R) (h : f a = f b) : f (a * c) = f (b * c) := by
  rw [map_mul, map_mul, h]

/-- The actual Galois action on A_cris multiplies t by the cyclotomic character. -/
theorem galois_t (σ : PeriodRing.PadicGalois p) :
    PeriodRing.acrisEquiv p (PeriodRing.galoisIntegerEquiv p σ) (PeriodRing.t p) =
      padicIntToAcris p (Galois.cyclotomicExponent p σ).val * PeriodRing.t p := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [Roots.galois_t_approx_eval]
  apply map_mul_of_map_eq
    (AdicCompletion.evalₐ (Ideal.span {(p : PeriodRing.AcrisZero p)}) n).toRingHom
    (Roots.cyclotomicApproximation p σ n : PeriodRing.Acris p)
    (padicIntToAcris p (Galois.cyclotomicExponent p σ).val) (PeriodRing.t p)
  exact (map_natCast
    (AdicCompletion.evalₐ (Ideal.span {(p : PeriodRing.AcrisZero p)}) n).toRingHom
    (Roots.cyclotomicApproximation p σ n)).trans
      (padicIntToAcris_approx_eval p (Galois.cyclotomicExponent p σ).val n).symm

theorem galois_bcrisPlus_t (σ : PeriodRing.PadicGalois p) :
    PeriodRing.bcrisPlusEquiv p (PeriodRing.galoisIntegerEquiv p σ)
        (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p)) =
      PeriodRing.padicIntToBcrisPlus p (Galois.cyclotomicExponent p σ).val *
        algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p) := by
  rw [PeriodRing.bcrisPlusEquiv_algebraMap, galois_t, map_mul, padicIntToAcris_bcrisPlus]

theorem galois_t_isUnit (σ : PeriodRing.PadicGalois p) :
    IsUnit (((algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p)).comp
        (PeriodRing.bcrisPlusEquiv p (PeriodRing.galoisIntegerEquiv p σ)).toRingHom)
      (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p))) := by
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    galois_bcrisPlus_t, map_mul]
  exact (((Galois.cyclotomicExponent p σ).isUnit.map (PeriodRing.padicIntToBcrisPlus p)).map
    (algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p))).mul (PeriodRing.t_isUnit_bcris p)

/-- The Galois map extends through inversion of the actual cyclotomic period. -/
def bcrisGaloisMap (σ : PeriodRing.PadicGalois p) : PeriodRing.Bcris p →+* PeriodRing.Bcris p :=
  Localization.awayLift
    ((algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p)).comp
      (PeriodRing.bcrisPlusEquiv p (PeriodRing.galoisIntegerEquiv p σ)).toRingHom)
    (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p)) (galois_t_isUnit p σ)

@[simp]
theorem bcrisGaloisMap_algebraMap (σ : PeriodRing.PadicGalois p) (x : PeriodRing.BcrisPlus p) :
    bcrisGaloisMap p σ (algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) x) =
      algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) (PeriodRing.bcrisPlusEquiv p (PeriodRing.galoisIntegerEquiv p σ) x) :=
  IsLocalization.Away.lift_eq _ (galois_t_isUnit p σ) x

theorem bcrisGaloisMap_one : bcrisGaloisMap p 1 = RingHom.id (PeriodRing.Bcris p) := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p)))
  apply RingHom.ext
  intro x
  change bcrisGaloisMap p 1 (algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) x) =
    algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) x
  rw [bcrisGaloisMap_algebraMap]
  exact congrArg (algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p))
    (DFunLike.congr_fun (Galois.galoisBcrisPlusAction p).map_one x)

theorem bcrisGaloisMap_mul (σ τ : PeriodRing.PadicGalois p) :
    bcrisGaloisMap p (σ * τ) = (bcrisGaloisMap p σ).comp (bcrisGaloisMap p τ) := by
  exact awayLifts_comp (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p))
    (bcrisGaloisMap p σ) (bcrisGaloisMap p τ) (bcrisGaloisMap p (σ * τ))
    (PeriodRing.bcrisPlusEquiv p (PeriodRing.galoisIntegerEquiv p σ)).toRingHom
    (PeriodRing.bcrisPlusEquiv p (PeriodRing.galoisIntegerEquiv p τ)).toRingHom
    (PeriodRing.bcrisPlusEquiv p (PeriodRing.galoisIntegerEquiv p (σ * τ))).toRingHom
    (bcrisGaloisMap_algebraMap p σ) (bcrisGaloisMap_algebraMap p τ)
    (bcrisGaloisMap_algebraMap p (σ * τ))
    (fun x => DFunLike.congr_fun ((Galois.galoisBcrisPlusAction p).map_mul σ τ) x)

def bcrisGaloisEquiv (σ : PeriodRing.PadicGalois p) : PeriodRing.Bcris p ≃+* PeriodRing.Bcris p :=
  { bcrisGaloisMap p σ with
    invFun := bcrisGaloisMap p σ⁻¹
    left_inv := fun x => by
      have h := bcrisGaloisMap_mul p σ⁻¹ σ
      rw [inv_mul_cancel, bcrisGaloisMap_one] at h
      exact (DFunLike.congr_fun h x).symm
    right_inv := fun x => by
      have h := bcrisGaloisMap_mul p σ σ⁻¹
      rw [mul_inv_cancel, bcrisGaloisMap_one] at h
      exact (DFunLike.congr_fun h x).symm }

theorem bcrisGaloisMap_padicField (σ : PeriodRing.PadicGalois p) (a : ℚ_[p]) :
    bcrisGaloisMap p σ (PeriodRing.padicFieldToBcris p a) = PeriodRing.padicFieldToBcris p a := by
  change bcrisGaloisMap p σ
      (algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) (PeriodRing.padicFieldToBcrisPlus p a)) =
    algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) (PeriodRing.padicFieldToBcrisPlus p a)
  rw [bcrisGaloisMap_algebraMap, PeriodRing.bcrisPlusEquiv_padicField]

def bcrisGaloisAlgEquiv (σ : PeriodRing.PadicGalois p) : PeriodRing.Bcris p ≃ₐ[ℚ_[p]] PeriodRing.Bcris p :=
  { bcrisGaloisEquiv p σ with
    commutes' := bcrisGaloisMap_padicField p σ }

/-- The absolute Galois group acts on the actual ring A_cris[1/p,1/t]. -/
def galoisBcrisAction : PeriodRing.PadicGalois p →* (PeriodRing.Bcris p ≃ₐ[ℚ_[p]] PeriodRing.Bcris p) where
  toFun := bcrisGaloisAlgEquiv p
  map_one' := by
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun (bcrisGaloisMap_one p) x
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun (bcrisGaloisMap_mul p σ τ) x

/-- The extended Galois action commutes with the extended Frobenius. -/
theorem galoisBcrisAction_frobenius (σ : PeriodRing.PadicGalois p) (x : PeriodRing.Bcris p) :
    galoisBcrisAction p σ (Cyclotomic.bcrisFrobenius p x) =
      Cyclotomic.bcrisFrobenius p (galoisBcrisAction p σ x) := by
  have h : (bcrisGaloisMap p σ).comp (Cyclotomic.bcrisFrobenius p) =
      (Cyclotomic.bcrisFrobenius p).comp (bcrisGaloisMap p σ) :=
    awayLifts_commute (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p))
      (bcrisGaloisMap p σ) (Cyclotomic.bcrisFrobenius p)
      (PeriodRing.bcrisPlusEquiv p (PeriodRing.galoisIntegerEquiv p σ)).toRingHom
      (AdicEstimates.Frobenius.bcrisPlusFrobenius p)
      (bcrisGaloisMap_algebraMap p σ) (Cyclotomic.bcrisFrobenius_algebraMap p)
      (Galois.bcrisPlusAction_frobenius p (PeriodRing.galoisIntegerEquiv p σ))
  exact DFunLike.congr_fun h x

end NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.Galois

namespace NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.RootCoordinates

/-!
# Coordinates of compatible root towers

A primitive compatible root sequence provides a p-adic coordinate for every
root tower. The coordinate is constructed from finite exponents and their
proved congruences. This also compares PeriodInvariants's and WeakAdmissibility's chosen periods.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.Galois OAI.NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.Roots OAI.NumberTheory.PadicHodge.PeriodInvariants.Cyclotomic OAI.NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.Galois

variable (p : ℕ) [Fact p.Prime]

theorem rootValue_pow (x : Roots.RootTower p) (n : ℕ) :
    Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (Roots.rootValue p x) ^ p ^ n = 1 :=
  (Perfection.coeffMonoidHom_pow_p_pow_self (Roots.rootValue p x) n).trans (Roots.rootValue_zero p x)

theorem exists_rootIndex (x : Roots.RootTower p) (n : ℕ) :
    ∃ i < p ^ n, PeriodRing.cyclotomicRootSequence p n ^ i =
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (Roots.rootValue p x) :=
  (Galois.cyclotomicRootSequence_primitive p n).eq_pow_of_pow_eq_one (rootValue_pow p x n)

def rootIndex (x : Roots.RootTower p) (n : ℕ) : ℕ := (exists_rootIndex p x n).choose

theorem rootIndex_lt (x : Roots.RootTower p) (n : ℕ) : rootIndex p x n < p ^ n :=
  (exists_rootIndex p x n).choose_spec.1

theorem rootIndex_spec (x : Roots.RootTower p) (n : ℕ) :
    PeriodRing.cyclotomicRootSequence p n ^ rootIndex p x n =
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (Roots.rootValue p x) :=
  (exists_rootIndex p x n).choose_spec.2

theorem rootIndex_succ_power (x : Roots.RootTower p) (n : ℕ) :
    PeriodRing.cyclotomicRootSequence p n ^ rootIndex p x (n + 1) =
      PeriodRing.cyclotomicRootSequence p n ^ rootIndex p x n := by
  calc
    PeriodRing.cyclotomicRootSequence p n ^ rootIndex p x (n + 1) =
        (PeriodRing.cyclotomicRootSequence p (n + 1) ^ p) ^ rootIndex p x (n + 1) := by
      rw [PeriodRing.cyclotomicRootSequence_compatible]
    _ = (PeriodRing.cyclotomicRootSequence p (n + 1) ^ rootIndex p x (n + 1)) ^ p := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm p]
    _ = Perfection.coeffMonoidHom 𝓞_ℂ_[p] p (n + 1) (Roots.rootValue p x) ^ p := by
      rw [rootIndex_spec]
    _ = Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (Roots.rootValue p x) :=
      Perfection.coeffMonoidHom_pow_p' (Roots.rootValue p x) n
    _ = PeriodRing.cyclotomicRootSequence p n ^ rootIndex p x n := (rootIndex_spec p x n).symm

theorem rootIndex_modEq (x : Roots.RootTower p) (n : ℕ) :
    rootIndex p x n ≡ rootIndex p x (n + 1) [MOD p ^ n] := by
  have hprim := Galois.cyclotomicRootSequence_primitive p n
  have h := (hprim.isOfFinOrder (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).pow_eq_pow_iff_modEq.mp
    (rootIndex_succ_power p x n).symm
  rwa [← hprim.eq_orderOf] at h

theorem rootIndex_int_compatible (x : Roots.RootTower p) (n : ℕ) :
    (p : ℤ) ^ n ∣ (rootIndex p x (n + 1) : ℤ) - (rootIndex p x n : ℤ) := by
  simpa only [Nat.cast_pow] using (rootIndex_modEq p x n).dvd

def rootExponent (x : Roots.RootTower p) : ℤ_[p] :=
  PadicInt.ofIntSeq (fun n => (rootIndex p x n : ℤ))
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (fun n => (rootIndex p x n : ℤ)) p (rootIndex_int_compatible p x))

theorem rootExponent_mod (x : Roots.RootTower p) (n : ℕ) :
    (rootExponent p x).toZModPow n = (rootIndex p x n : ZMod (p ^ n)) := by
  simpa only [rootExponent, Int.cast_natCast] using PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
    (fun n => (rootIndex p x n : ℤ)) p (rootIndex_int_compatible p x) n

theorem rootExponent_approx (x : Roots.RootTower p) (n : ℕ) :
    ((rootExponent p x).toZModPow n).val = rootIndex p x n := by
  rw [rootExponent_mod, ZMod.val_natCast, Nat.mod_eq_of_lt (rootIndex_lt p x n)]

/-- Every actual root-tower logarithm is its p-adic coordinate times the chosen period. -/
theorem rootLog_eq_exponent_mul_t (x : Roots.RootTower p) :
    Roots.rootLog p x = Galois.padicIntToAcris p (rootExponent p x) * PeriodRing.t p := by
  apply AdicCompletion.ext_evalₐ
  intro n
  have hc : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n (Roots.rootValue p x) =
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n
        (Roots.rootValue p (Roots.cyclotomicRootTower p ^ rootIndex p x n)) := (rootIndex_spec p x n).symm
  have h := Roots.rootLog_congr_eval p x (Roots.cyclotomicRootTower p ^ rootIndex p x n) n hc
  rw [Roots.rootLog_pow, Roots.cyclotomicRootTower_log] at h
  refine h.trans ?_
  apply Galois.map_mul_of_map_eq
    (AdicCompletion.evalₐ (Ideal.span {(p : PeriodRing.AcrisZero p)}) n).toRingHom
    (rootIndex p x n : PeriodRing.Acris p) (Galois.padicIntToAcris p (rootExponent p x)) (PeriodRing.t p)
  have hs := Galois.padicIntToAcris_approx_eval p (rootExponent p x) n
  rw [rootExponent_approx] at hs
  exact (map_natCast
    (AdicCompletion.evalₐ (Ideal.span {(p : PeriodRing.AcrisZero p)}) n).toRingHom
    (rootIndex p x n)).trans hs.symm

theorem rootExponent_isUnit (x : Roots.RootTower p)
    (hx : IsPrimitiveRoot (Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 1 (Roots.rootValue p x)) p) :
    IsUnit (rootExponent p x) := by
  have hprim : IsPrimitiveRoot (PeriodRing.primitiveRootInteger p ^ rootIndex p x 1) p := by
    change IsPrimitiveRoot (PeriodRing.cyclotomicRootSequence p 1 ^ rootIndex p x 1) p
    rw [rootIndex_spec]
    exact hx
  have hcop := ((PeriodRing.primitiveRootInteger_primitive p).pow_iff_coprime
    (Fact.out : p.Prime).pos (rootIndex p x 1)).mp hprim
  have hnd : ¬p ∣ rootIndex p x 1 :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop.symm
  by_contra hu
  have hd : (p : ℤ_[p]) ∣ rootExponent p x :=
    (PadicInt.norm_lt_one_iff_dvd (rootExponent p x)).mp (PadicInt.not_isUnit_iff.mp hu)
  have hz : (rootExponent p x).toZModPow 1 = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton, pow_one]
    exact hd
  rw [rootExponent_mod] at hz
  have hdiv := (ZMod.natCast_eq_zero_iff (rootIndex p x 1) (p ^ 1)).mp hz
  exact hnd (by simpa only [pow_one] using hdiv)

def e63RootTower : Roots.RootTower p := Roots.rootTowerOfSequence p (WeakAdmissibility.Logarithm.PeriodRings.cyclotomicTower p) rfl

theorem e63RootTower_primitive :
    IsPrimitiveRoot (Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 1 (Roots.rootValue p (e63RootTower p))) p := by
  change IsPrimitiveRoot (WeakAdmissibility.Logarithm.PeriodRings.firstCyclotomicInteger p) p
  constructor
  · exact WeakAdmissibility.Logarithm.PeriodRings.firstCyclotomicInteger_pow p
  · intro n hn
    exact (WeakAdmissibility.Logarithm.PeriodRings.firstCyclotomicRoot_primitive p).dvd_of_pow_eq_one n
      (congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) hn)

def periodRatio : ℤ_[p]ˣ := (rootExponent_isUnit p (e63RootTower p) (e63RootTower_primitive p)).unit

/-- The chosen WeakAdmissibility period maps to a p-adic unit multiple of the chosen PeriodInvariants period. -/
theorem comparison_cyclotomicPeriod :
    Cyclotomic.acrisComparison p (WeakAdmissibility.Logarithm.PeriodRings.cyclotomicPeriod p) =
      Galois.padicIntToAcris p (periodRatio p).val * PeriodRing.t p :=
  (Cyclotomic.acrisComparison_log p (Roots.rootKernelElement p (e63RootTower p))).trans
    (rootLog_eq_exponent_mul_t p (e63RootTower p))

end NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.RootCoordinates

namespace NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.PeriodBridge

/-!
# The concrete PeriodInvariants–WeakAdmissibility bridge after inversion of the periods

The two chosen cyclotomic periods differ by the proved p-adic unit ratio.
Localization therefore extends the completed-envelope comparison to B_cris.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicEstimates.Frobenius OAI.NumberTheory.PadicHodge.PeriodInvariants.Cyclotomic OAI.NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.Galois OAI.NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.RootCoordinates

section Localization

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']

def pLocalizationEquiv (p : ℕ) (e : R ≃+* S) :
    Localization.Away (p : R) ≃+* Localization.Away (p : S) :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (p : R)) (T := Submonoid.powers (p : S))
    (Localization.Away (p : R)) (Localization.Away (p : S)) e
    (by
      rw [Submonoid.map_powers]
      change Submonoid.powers (e (p : R)) = Submonoid.powers (p : S)
      rw [map_natCast])

theorem pLocalizationEquiv_algebraMap (p : ℕ) (e : R ≃+* S) (x : R) :
    pLocalizationEquiv p e (algebraMap R (Localization.Away (p : R)) x) =
      algebraMap S (Localization.Away (p : S)) (e x) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ x

def awayEquivOfAssociated (e : R ≃+* S) (r : R) (s : S) (h : Associated s (e r)) :
    Localization.Away r ≃+* Localization.Away s := by
  letI : IsLocalization.Away (e r) (Localization.Away s) :=
    IsLocalization.Away.of_associated h
  exact IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers r) (T := Submonoid.powers (e r))
    (Localization.Away r) (Localization.Away s) e
    (by rw [Submonoid.map_powers]; rfl)

theorem awayEquivOfAssociated_algebraMap (e : R ≃+* S) (r : R) (s : S)
    (h : Associated s (e r)) (x : R) :
    awayEquivOfAssociated e r s h (algebraMap R (Localization.Away r) x) =
      algebraMap S (Localization.Away s) (e x) := by
  let _ : IsLocalization.Away (e r) (Localization.Away s) :=
    IsLocalization.Away.of_associated h
  exact IsLocalization.ringEquivOfRingEquiv_eq
    (M := Submonoid.powers r) (T := Submonoid.powers (e r))
    (by rw [Submonoid.map_powers]; rfl) x

variable [Algebra R R'] [Algebra S S']

theorem localization_natural (M : Submonoid R) [IsLocalization M R']
    (e : R →+* S) (E : R' →+* S') (f : R →+* R) (g : S →+* S)
    (F : R' →+* R') (G : S' →+* S')
    (hE : ∀ x, E (algebraMap R R' x) = algebraMap S S' (e x))
    (hF : ∀ x, F (algebraMap R R' x) = algebraMap R R' (f x))
    (hG : ∀ x, G (algebraMap S S' x) = algebraMap S S' (g x))
    (hfg : ∀ x, e (f x) = g (e x)) (x : R') : E (F x) = G (E x) := by
  have h : E.comp F = G.comp E := by
    apply IsLocalization.ringHom_ext (M := M)
    apply RingHom.ext
    intro a
    change E (F (algebraMap R R' a)) = G (E (algebraMap R R' a))
    rw [hF, hE, hE, hG, hfg]
  exact DFunLike.congr_fun h x

end Localization

theorem pLocalizationEquiv_completedSubalgebra (p : ℕ)
    {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]
    (U V : Subalgebra A L) (h : U = V) :
    pLocalizationEquiv p (WeakAdmissibilityBridge.completedSubalgebraEquiv p U V h) =
      WeakAdmissibilityBridge.positiveSubalgebraEquiv p U V h := by
  subst V
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers (p : AdicCompletion (Ideal.span {(p : U)}) U))
  apply RingHom.ext
  intro x
  change pLocalizationEquiv p (RingEquiv.refl _)
      (algebraMap _ (Localization.Away (p : AdicCompletion (Ideal.span {(p : U)}) U)) x) = _
  rw [pLocalizationEquiv_algebraMap]
  rfl

variable (p : ℕ) [Fact p.Prime]

def positiveComparison : WeakAdmissibility.Logarithm.PeriodRings.BCrisPlus p ≃+* PeriodRing.BcrisPlus p :=
  pLocalizationEquiv p (Cyclotomic.acrisComparison p)

theorem positiveComparison_eq : positiveComparison p = WeakAdmissibilityBridge.bcrisPlusEquiv p :=
  (congrArg (fun e : WeakAdmissibility.Logarithm.PeriodRings.ACris p ≃+* PeriodRing.Acris p => pLocalizationEquiv p e)
    (Cyclotomic.acrisComparison_eq p)).trans
    (pLocalizationEquiv_completedSubalgebra p (WeakAdmissibility.Logarithm.PeriodRings.aCrisUncompleted p)
      (PeriodRing.acrisZeroSubalgebra p) (WeakAdmissibilityBridge.envelopes_eq p))

theorem positiveComparison_algebraMap (x : WeakAdmissibility.Logarithm.PeriodRings.ACris p) :
    positiveComparison p (algebraMap (WeakAdmissibility.Logarithm.PeriodRings.ACris p) (WeakAdmissibility.Logarithm.PeriodRings.BCrisPlus p) x) =
      algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (Cyclotomic.acrisComparison p x) :=
  pLocalizationEquiv_algebraMap p (Cyclotomic.acrisComparison p) x

theorem positiveComparison_frobenius (x : WeakAdmissibility.Logarithm.PeriodRings.BCrisPlus p) :
    positiveComparison p (WeakAdmissibility.Logarithm.PeriodRings.bCrisPlusFrobenius p x) =
      AdicEstimates.Frobenius.bcrisPlusFrobenius p (positiveComparison p x) :=
  localization_natural (Submonoid.powers (p : WeakAdmissibility.Logarithm.PeriodRings.ACris p))
    (Cyclotomic.acrisComparison p).toRingHom (positiveComparison p).toRingHom
    (WeakAdmissibility.Logarithm.PeriodRings.aCrisFrobenius p) (AdicEstimates.Frobenius.acrisFrobenius p)
    (WeakAdmissibility.Logarithm.PeriodRings.bCrisPlusFrobenius p) (AdicEstimates.Frobenius.bcrisPlusFrobenius p)
    (positiveComparison_algebraMap p) (WeakAdmissibility.Logarithm.PeriodRings.bCrisPlusFrobenius_algebraMap p)
    (AdicEstimates.Frobenius.bcrisPlusFrobenius_algebraMap p) (Cyclotomic.acrisComparison_frobenius p) x

theorem positiveComparison_period :
    positiveComparison p
        (algebraMap (WeakAdmissibility.Logarithm.PeriodRings.ACris p) (WeakAdmissibility.Logarithm.PeriodRings.BCrisPlus p)
          (WeakAdmissibility.Logarithm.PeriodRings.cyclotomicPeriod p)) =
      PeriodRing.padicIntToBcrisPlus p (RootCoordinates.periodRatio p).val *
        algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p) := by
  rw [positiveComparison_algebraMap, RootCoordinates.comparison_cyclotomicPeriod, map_mul,
    Galois.padicIntToAcris_bcrisPlus]

theorem positiveComparison_period_associated :
    Associated (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p))
      (positiveComparison p
        (algebraMap (WeakAdmissibility.Logarithm.PeriodRings.ACris p) (WeakAdmissibility.Logarithm.PeriodRings.BCrisPlus p)
          (WeakAdmissibility.Logarithm.PeriodRings.cyclotomicPeriod p))) := by
  rw [positiveComparison_period]
  exact (associated_unit_mul_left (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p))
    (PeriodRing.padicIntToBcrisPlus p (RootCoordinates.periodRatio p).val)
    ((RootCoordinates.periodRatio p).isUnit.map (PeriodRing.padicIntToBcrisPlus p))).symm

/-- The comparison of the actual crystalline period rings after inversion of t. -/
def bcrisComparison : WeakAdmissibility.Logarithm.PeriodRings.BCris p ≃+* PeriodRing.Bcris p :=
  awayEquivOfAssociated (positiveComparison p)
    (algebraMap (WeakAdmissibility.Logarithm.PeriodRings.ACris p) (WeakAdmissibility.Logarithm.PeriodRings.BCrisPlus p)
      (WeakAdmissibility.Logarithm.PeriodRings.cyclotomicPeriod p))
    (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p)) (positiveComparison_period_associated p)

theorem bcrisComparison_algebraMap (x : WeakAdmissibility.Logarithm.PeriodRings.BCrisPlus p) :
    bcrisComparison p (algebraMap (WeakAdmissibility.Logarithm.PeriodRings.BCrisPlus p) (WeakAdmissibility.Logarithm.PeriodRings.BCris p) x) =
      algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) (positiveComparison p x) :=
  awayEquivOfAssociated_algebraMap (positiveComparison p)
    (algebraMap (WeakAdmissibility.Logarithm.PeriodRings.ACris p) (WeakAdmissibility.Logarithm.PeriodRings.BCrisPlus p)
      (WeakAdmissibility.Logarithm.PeriodRings.cyclotomicPeriod p))
    (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p)) (positiveComparison_period_associated p) x

theorem bcrisComparison_frobenius (x : WeakAdmissibility.Logarithm.PeriodRings.BCris p) :
    bcrisComparison p (WeakAdmissibility.Logarithm.bCrisFrobenius p x) =
      Cyclotomic.bcrisFrobenius p (bcrisComparison p x) :=
  localization_natural
    (Submonoid.powers (algebraMap (WeakAdmissibility.Logarithm.PeriodRings.ACris p) (WeakAdmissibility.Logarithm.PeriodRings.BCrisPlus p)
      (WeakAdmissibility.Logarithm.PeriodRings.cyclotomicPeriod p)))
    (positiveComparison p).toRingHom (bcrisComparison p).toRingHom
    (WeakAdmissibility.Logarithm.PeriodRings.bCrisPlusFrobenius p) (AdicEstimates.Frobenius.bcrisPlusFrobenius p)
    (WeakAdmissibility.Logarithm.bCrisFrobenius p) (Cyclotomic.bcrisFrobenius p)
    (bcrisComparison_algebraMap p) (WeakAdmissibility.Logarithm.bCrisFrobenius_algebraMap p)
    (Cyclotomic.bcrisFrobenius_algebraMap p) (positiveComparison_frobenius p) x

end NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.PeriodBridge

end

end OAI
