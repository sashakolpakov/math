import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicEstimates

/-! # Galois -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.Galois

noncomputable section

/-!
# Galois action and Frobenius commutation on the concrete positive period rings

The maps are the automorphisms constructed from the action on the completed
algebraic closure. This file proves their group laws and commutation relations.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicEstimates.Frobenius

variable (p : ℕ) [Fact p.Prime]

def ainfAction : (𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) →* (PeriodRing.Ainf p ≃+* PeriodRing.Ainf p) where
  toFun := PeriodRing.ainfEquiv p
  map_one' := by
    apply RingEquiv.toRingHom_injective
    exact PeriodRing.ainfMap_id p
  map_mul' f g := by
    apply RingEquiv.toRingHom_injective
    exact PeriodRing.ainfMap_comp p g.toRingHom f.toRingHom

def fractionAction : (𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) →*
    (FractionRing (PeriodRing.Ainf p) ≃+* FractionRing (PeriodRing.Ainf p)) :=
  (IsFractionRing.ringEquivOfRingEquivHom (PeriodRing.Ainf p) (FractionRing (PeriodRing.Ainf p))).comp
    (ainfAction p)

def acrisZeroAction : (𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) →* (PeriodRing.AcrisZero p ≃+* PeriodRing.AcrisZero p) where
  toFun := PeriodRing.acrisZeroEquiv p
  map_one' := by
    apply RingEquiv.ext
    intro x
    apply Subtype.val_injective
    exact DFunLike.congr_fun (fractionAction p).map_one (x : FractionRing (PeriodRing.Ainf p))
  map_mul' f g := by
    apply RingEquiv.ext
    intro x
    apply Subtype.val_injective
    exact DFunLike.congr_fun ((fractionAction p).map_mul f g) (x : FractionRing (PeriodRing.Ainf p))

section Completion

omit [Fact p.Prime]
variable {R : Type*} [CommRing R]

def pAdicAction : (R ≃+* R) →*
    (AdicCompletion (Ideal.span {(p : R)}) R ≃+*
      AdicCompletion (Ideal.span {(p : R)}) R) where
  toFun := PeriodRing.pAdicEquiv p
  map_one' := by
    apply RingEquiv.toRingHom_injective
    exact PeriodRing.pAdicMap_id p
  map_mul' f g := by
    apply RingEquiv.toRingHom_injective
    exact PeriodRing.pAdicMap_comp p g.toRingHom f.toRingHom

theorem pAdicMap_commute (f g : R →+* R) (h : ∀ x, f (g x) = g (f x))
    (x : AdicCompletion (Ideal.span {(p : R)}) R) :
    PeriodRing.pAdicMap p f (PeriodRing.pAdicMap p g x) = PeriodRing.pAdicMap p g (PeriodRing.pAdicMap p f x) := by
  have he : f.comp g = g.comp f := RingHom.ext h
  have hc := congrArg (PeriodRing.pAdicMap p) he
  rw [PeriodRing.pAdicMap_comp, PeriodRing.pAdicMap_comp] at hc
  exact DFunLike.congr_fun hc x

end Completion

def acrisAction : (𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) →* (PeriodRing.Acris p ≃+* PeriodRing.Acris p) :=
  (pAdicAction p).comp (acrisZeroAction p)

def bcrisPlusAction : (𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) →* (PeriodRing.BcrisPlus p ≃+* PeriodRing.BcrisPlus p) where
  toFun := PeriodRing.bcrisPlusEquiv p
  map_one' := by
    apply RingEquiv.toRingHom_injective
    apply IsLocalization.ringHom_ext (M := Submonoid.powers (p : PeriodRing.Acris p))
    apply RingHom.ext
    intro x
    change PeriodRing.bcrisPlusEquiv p 1 (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) x) =
      algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) x
    rw [PeriodRing.bcrisPlusEquiv_algebraMap]
    exact congrArg (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p))
      (DFunLike.congr_fun (acrisAction p).map_one x)
  map_mul' f g := by
    apply RingEquiv.toRingHom_injective
    apply IsLocalization.ringHom_ext (M := Submonoid.powers (p : PeriodRing.Acris p))
    apply RingHom.ext
    intro x
    change PeriodRing.bcrisPlusEquiv p (f * g) (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) x) =
      PeriodRing.bcrisPlusEquiv p f (PeriodRing.bcrisPlusEquiv p g (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) x))
    rw [PeriodRing.bcrisPlusEquiv_algebraMap, PeriodRing.bcrisPlusEquiv_algebraMap, PeriodRing.bcrisPlusEquiv_algebraMap]
    exact congrArg (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p))
      (DFunLike.congr_fun ((acrisAction p).map_mul f g) x)

def bcrisPlusAlgebraAction : (𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) →*
    (PeriodRing.BcrisPlus p ≃ₐ[ℚ_[p]] PeriodRing.BcrisPlus p) where
  toFun := PeriodRing.bcrisPlusAlgEquiv p
  map_one' := by
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun (bcrisPlusAction p).map_one x
  map_mul' f g := by
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun ((bcrisPlusAction p).map_mul f g) x

theorem ainfMap_frobenius (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (x : PeriodRing.Ainf p) :
    PeriodRing.ainfMap p f (AdicEstimates.Frobenius.ainfFrobenius p x) = AdicEstimates.Frobenius.ainfFrobenius p (PeriodRing.ainfMap p f x) := by
  apply WittVector.ext
  intro n
  change PeriodRing.tiltMap p f ((WittVector.frobenius x).coeff n) =
    (WittVector.frobenius (WittVector.map (PeriodRing.tiltMap p f) x)).coeff n
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP,
    WittVector.map_coeff, map_pow]

theorem fractionAction_frobenius (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p])
    (x : FractionRing (PeriodRing.Ainf p)) :
    PeriodRing.ainfFractionEquiv p f (AdicEstimates.Frobenius.fractionFrobenius p x) =
      AdicEstimates.Frobenius.fractionFrobenius p (PeriodRing.ainfFractionEquiv p f x) := by
  have h : (PeriodRing.ainfFractionEquiv p f).toRingHom.comp (AdicEstimates.Frobenius.fractionFrobenius p).toRingHom =
      (AdicEstimates.Frobenius.fractionFrobenius p).toRingHom.comp (PeriodRing.ainfFractionEquiv p f).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := PeriodRing.Ainf p)
    intro a
    change PeriodRing.ainfFractionEquiv p f
        (AdicEstimates.Frobenius.fractionFrobenius p (algebraMap (PeriodRing.Ainf p) (FractionRing (PeriodRing.Ainf p)) a)) =
      AdicEstimates.Frobenius.fractionFrobenius p
        (PeriodRing.ainfFractionEquiv p f (algebraMap (PeriodRing.Ainf p) (FractionRing (PeriodRing.Ainf p)) a))
    rw [AdicEstimates.Frobenius.fractionFrobenius_algebraMap, PeriodRing.ainfFractionEquiv_algebraMap,
      PeriodRing.ainfFractionEquiv_algebraMap, AdicEstimates.Frobenius.fractionFrobenius_algebraMap, ainfMap_frobenius]
  exact DFunLike.congr_fun h x

theorem acrisZeroAction_frobenius (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : PeriodRing.AcrisZero p) :
    PeriodRing.acrisZeroMap p f (AdicEstimates.Frobenius.acrisZeroFrobenius p x) =
      AdicEstimates.Frobenius.acrisZeroFrobenius p (PeriodRing.acrisZeroMap p f x) :=
  Subtype.ext (fractionAction_frobenius p f x)

theorem acrisAction_frobenius (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : PeriodRing.Acris p) :
    PeriodRing.acrisEquiv p f (AdicEstimates.Frobenius.acrisFrobenius p x) = AdicEstimates.Frobenius.acrisFrobenius p (PeriodRing.acrisEquiv p f x) :=
  pAdicMap_commute p (PeriodRing.acrisZeroMap p f) (AdicEstimates.Frobenius.acrisZeroFrobenius p)
    (acrisZeroAction_frobenius p f) x

theorem bcrisPlusAction_frobenius (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : PeriodRing.BcrisPlus p) :
    PeriodRing.bcrisPlusEquiv p f (AdicEstimates.Frobenius.bcrisPlusFrobenius p x) =
      AdicEstimates.Frobenius.bcrisPlusFrobenius p (PeriodRing.bcrisPlusEquiv p f x) := by
  have h : (PeriodRing.bcrisPlusEquiv p f).toRingHom.comp (AdicEstimates.Frobenius.bcrisPlusFrobenius p) =
      (AdicEstimates.Frobenius.bcrisPlusFrobenius p).comp (PeriodRing.bcrisPlusEquiv p f).toRingHom := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers (p : PeriodRing.Acris p))
    apply RingHom.ext
    intro a
    change PeriodRing.bcrisPlusEquiv p f
        (AdicEstimates.Frobenius.bcrisPlusFrobenius p (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) a)) =
      AdicEstimates.Frobenius.bcrisPlusFrobenius p
        (PeriodRing.bcrisPlusEquiv p f (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) a))
    rw [AdicEstimates.Frobenius.bcrisPlusFrobenius_algebraMap, PeriodRing.bcrisPlusEquiv_algebraMap,
      PeriodRing.bcrisPlusEquiv_algebraMap, AdicEstimates.Frobenius.bcrisPlusFrobenius_algebraMap, acrisAction_frobenius]
  exact DFunLike.congr_fun h x

/-- Group laws for the Galois action on the actual ring of integers. -/
def galoisIntegerAction : PeriodRing.PadicGalois p →* (𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) where
  toFun := PeriodRing.galoisIntegerEquiv p
  map_one' := by
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    change UniformSpace.Completion.mapRingHom (RingHom.id (PadicAlgCl p)) continuous_id
      (x : ℂ_[p]) = (x : ℂ_[p])
    rw [UniformSpace.Completion.mapRingHom_id]
    rfl
  map_mul' σ τ := by
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    change UniformSpace.Completion.mapRingHom
        (σ.toRingEquiv.toRingHom.comp τ.toRingEquiv.toRingHom)
        ((PeriodRing.algebraicGalois_isometry p σ).continuous.comp
          (PeriodRing.algebraicGalois_isometry p τ).continuous) (x : ℂ_[p]) =
      UniformSpace.Completion.mapRingHom σ.toRingEquiv.toRingHom
        (PeriodRing.algebraicGalois_isometry p σ).continuous
        (UniformSpace.Completion.mapRingHom τ.toRingEquiv.toRingHom
          (PeriodRing.algebraicGalois_isometry p τ).continuous (x : ℂ_[p]))
    exact (congrArg (fun h : ℂ_[p] →+* ℂ_[p] => h (x : ℂ_[p]))
      (UniformSpace.Completion.mapRingHom_comp
        (f := τ.toRingEquiv.toRingHom) (g := σ.toRingEquiv.toRingHom)
        (PeriodRing.algebraicGalois_isometry p σ).continuous
        (PeriodRing.algebraicGalois_isometry p τ).continuous)).symm

/-- The actual absolute Galois action on the positive crystalline ring. -/
def galoisBcrisPlusAction : PeriodRing.PadicGalois p →* (PeriodRing.BcrisPlus p ≃ₐ[ℚ_[p]] PeriodRing.BcrisPlus p) :=
  (bcrisPlusAlgebraAction p).comp (galoisIntegerAction p)

theorem galoisBcrisPlusAction_frobenius (σ : PeriodRing.PadicGalois p) (x : PeriodRing.BcrisPlus p) :
    galoisBcrisPlusAction p σ (AdicEstimates.Frobenius.bcrisPlusFrobenius p x) =
      AdicEstimates.Frobenius.bcrisPlusFrobenius p (galoisBcrisPlusAction p σ x) :=
  bcrisPlusAction_frobenius p (PeriodRing.galoisIntegerEquiv p σ) x

def galoisComplexAction : PeriodRing.PadicGalois p →* (ℂ_[p] ≃+* ℂ_[p]) where
  toFun := PeriodRing.galoisComplexEquiv p
  map_one' := by
    apply RingEquiv.ext
    intro x
    change UniformSpace.Completion.mapRingHom (RingHom.id (PadicAlgCl p)) continuous_id x = x
    rw [UniformSpace.Completion.mapRingHom_id]
    rfl
  map_mul' σ τ := by
    apply RingEquiv.ext
    intro x
    change UniformSpace.Completion.mapRingHom
        (σ.toRingEquiv.toRingHom.comp τ.toRingEquiv.toRingHom)
        ((PeriodRing.algebraicGalois_isometry p σ).continuous.comp
          (PeriodRing.algebraicGalois_isometry p τ).continuous) x =
      UniformSpace.Completion.mapRingHom σ.toRingEquiv.toRingHom
        (PeriodRing.algebraicGalois_isometry p σ).continuous
        (UniformSpace.Completion.mapRingHom τ.toRingEquiv.toRingHom
          (PeriodRing.algebraicGalois_isometry p τ).continuous x)
    exact (congrArg (fun h : ℂ_[p] →+* ℂ_[p] => h x)
      (UniformSpace.Completion.mapRingHom_comp
        (f := τ.toRingEquiv.toRingHom) (g := σ.toRingEquiv.toRingHom)
        (PeriodRing.algebraicGalois_isometry p σ).continuous
        (PeriodRing.algebraicGalois_isometry p τ).continuous)).symm

/-- The cyclotomic character obtained from the actual action on roots of unity. -/
def cyclotomicExponent : PeriodRing.PadicGalois p →* ℤ_[p]ˣ :=
  (_root_.cyclotomicCharacter ℂ_[p] p).comp (galoisComplexAction p)

theorem cyclotomicRootSequence_pow (n : ℕ) :
    PeriodRing.cyclotomicRootSequence p n ^ p ^ n = 1 := by
  induction n with
  | zero => simp [PeriodRing.cyclotomicRootSequence]
  | succ n ih =>
      rw [pow_succ, Nat.mul_comm (p ^ n) p, pow_mul,
        PeriodRing.cyclotomicRootSequence_compatible, ih]

theorem cyclotomicRootSequence_pow_shift (m n : ℕ) :
    PeriodRing.cyclotomicRootSequence p (m + n) ^ p ^ m = PeriodRing.cyclotomicRootSequence p n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Nat.mul_comm (p ^ m) p, pow_mul,
        Nat.succ_add, PeriodRing.cyclotomicRootSequence_compatible, ih]

theorem cyclotomicRootSequence_primitive (n : ℕ) :
    IsPrimitiveRoot (PeriodRing.cyclotomicRootSequence p n) (p ^ n) := by
  cases n with
  | zero => simp [PeriodRing.cyclotomicRootSequence]
  | succ n =>
      have hnot : PeriodRing.cyclotomicRootSequence p (n + 1) ^ p ^ n ≠ 1 := by
        rw [cyclotomicRootSequence_pow_shift]
        exact (PeriodRing.primitiveRootInteger_primitive p).ne_one (Fact.out : p.Prime).one_lt
      have hord := orderOf_eq_prime_pow hnot (cyclotomicRootSequence_pow p (n + 1))
      rw [← hord]
      exact IsPrimitiveRoot.orderOf _

/-- The cyclotomic character describes the action on every member of the
chosen compatible root sequence. -/
theorem galois_cyclotomicRootSequence (σ : PeriodRing.PadicGalois p) (n : ℕ) :
    PeriodRing.galoisIntegerEquiv p σ (PeriodRing.cyclotomicRootSequence p n) =
      PeriodRing.cyclotomicRootSequence p n ^ (((cyclotomicExponent p σ).val).toZModPow n).val := by
  apply Subtype.val_injective
  exact _root_.cyclotomicCharacter.spec p (PeriodRing.galoisComplexEquiv p σ)
    (PeriodRing.cyclotomicRootSequence p n : ℂ_[p])
    (by exact_mod_cast cyclotomicRootSequence_pow p n)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.Galois
