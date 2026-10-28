import OAI.NumberTheory.PadicHodge.PeriodInvariants.NontrivialityT
import OAI.NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic

/-! # Crystalline Scalars -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineScalars

noncomputable section

section

/-!
# Canonical coefficients and fixed scalars of the actual crystalline ring

Frobenius fixes the constructed Q_p coefficients. For each actual Galois
subgroup, its fixed elements form a nontrivial Q_p-algebra on which Frobenius
acts. The identification of this algebra with K_0 is not assumed here.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicEstimates.Frobenius OAI.NumberTheory.PadicHodge.PeriodInvariants.Cyclotomic OAI.NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.Galois OAI.NumberTheory.PadicHodge.PeriodInvariants.NontrivialityT

section FixedAlgebra

variable {R B G : Type*} [CommRing R] [CommRing B] [Algebra R B] [Group G]

def fixedSubalgebra (σ : G →* (B ≃ₐ[R] B)) : Subalgebra R B where
  carrier := {a | ∀ g : G, σ g a = a}
  zero_mem' g := map_zero _
  one_mem' g := map_one _
  add_mem' ha hb g := by rw [map_add, ha g, hb g]
  mul_mem' ha hb g := by rw [map_mul, ha g, hb g]
  algebraMap_mem' a g := (σ g).commutes a

theorem map_mem_fixedSubalgebra (σ : G →* (B ≃ₐ[R] B)) (f : B →ₐ[R] B)
    (hf : ∀ g b, σ g (f b) = f (σ g b)) (b : fixedSubalgebra σ) :
    f b ∈ fixedSubalgebra σ := by
  intro g
  exact (hf g b).trans (congrArg f (b.property g))

def fixedSubalgebraMap (σ : G →* (B ≃ₐ[R] B)) (f : B →ₐ[R] B)
    (hf : ∀ g b, σ g (f b) = f (σ g b)) : fixedSubalgebra σ →ₐ[R] fixedSubalgebra σ where
  toFun b := ⟨f b, map_mem_fixedSubalgebra σ f hf b⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add f (a : B) b)
  map_mul' a b := Subtype.ext (map_mul f (a : B) b)
  commutes' a := Subtype.ext (f.commutes a)

end FixedAlgebra

variable (p : ℕ) [Fact p.Prime]

theorem legacy_bcris_nontrivial : Nontrivial (WeakAdmissibility.Logarithm.PeriodRings.BCris p) := by
  apply nontrivial_of_ne (0 : WeakAdmissibility.Logarithm.PeriodRings.BCris p) 1
  intro h
  have he := congrArg (TateCyclotomic.PeriodBridge.bcrisComparison p) h
  exact zero_ne_one (by simpa only [map_zero, map_one] using he)

theorem legacy_bcris_charZero : CharZero (WeakAdmissibility.Logarithm.PeriodRings.BCris p) where
  cast_injective a b h := by
    have he := congrArg (TateCyclotomic.PeriodBridge.bcrisComparison p) h
    simpa only [map_natCast, Nat.cast_inj] using he

theorem ainfFrobenius_padicInt (x : ℤ_[p]) :
    AdicEstimates.Frobenius.ainfFrobenius p (PeriodRing.padicIntToAinf p x) = PeriodRing.padicIntToAinf p x := by
  change WittVector.frobenius
      (WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p)) (WittVector.fromPadicInt p x)) =
    WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p)) (WittVector.fromPadicInt p x)
  ext n
  simp only [WittVector.coeff_frobenius_charP, WittVector.map_coeff]
  rw [← map_pow, ZMod.pow_card]

theorem acrisZeroFrobenius_algebraMap (x : PeriodRing.Ainf p) :
    AdicEstimates.Frobenius.acrisZeroFrobenius p (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) x) =
      algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) (AdicEstimates.Frobenius.ainfFrobenius p x) := by
  apply Subtype.ext
  exact AdicEstimates.Frobenius.fractionFrobenius_algebraMap p x

theorem acrisFrobenius_algebraMap (x : PeriodRing.AcrisZero p) :
    AdicEstimates.Frobenius.acrisFrobenius p (algebraMap (PeriodRing.AcrisZero p) (PeriodRing.Acris p) x) =
      algebraMap (PeriodRing.AcrisZero p) (PeriodRing.Acris p) (AdicEstimates.Frobenius.acrisZeroFrobenius p x) :=
  PeriodRing.pAdicMap_of p (AdicEstimates.Frobenius.acrisZeroFrobenius p) x

theorem bcrisPlusFrobenius_padicInt (x : ℤ_[p]) :
    AdicEstimates.Frobenius.bcrisPlusFrobenius p (PeriodRing.padicIntToBcrisPlus p x) = PeriodRing.padicIntToBcrisPlus p x := by
  change AdicEstimates.Frobenius.bcrisPlusFrobenius p (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p)
      (algebraMap (PeriodRing.AcrisZero p) (PeriodRing.Acris p)
        (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) (PeriodRing.padicIntToAinf p x)))) = _
  rw [AdicEstimates.Frobenius.bcrisPlusFrobenius_algebraMap, acrisFrobenius_algebraMap,
    acrisZeroFrobenius_algebraMap, ainfFrobenius_padicInt]
  rfl

theorem bcrisPlusFrobenius_padicField (x : ℚ_[p]) :
    AdicEstimates.Frobenius.bcrisPlusFrobenius p (PeriodRing.padicFieldToBcrisPlus p x) = PeriodRing.padicFieldToBcrisPlus p x := by
  have he : (AdicEstimates.Frobenius.bcrisPlusFrobenius p).comp (PeriodRing.padicFieldToBcrisPlus p) = PeriodRing.padicFieldToBcrisPlus p := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    ext a
    change AdicEstimates.Frobenius.bcrisPlusFrobenius p (PeriodRing.padicFieldToBcrisPlus p (algebraMap ℤ_[p] ℚ_[p] a)) = _
    rw [PeriodRing.padicFieldToBcrisPlus_int, bcrisPlusFrobenius_padicInt]
    exact (PeriodRing.padicFieldToBcrisPlus_int p a).symm
  exact DFunLike.congr_fun he x

theorem bcrisFrobenius_padicField (x : ℚ_[p]) :
    Cyclotomic.bcrisFrobenius p (PeriodRing.padicFieldToBcris p x) = PeriodRing.padicFieldToBcris p x := by
  change Cyclotomic.bcrisFrobenius p (algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) (PeriodRing.padicFieldToBcrisPlus p x)) = _
  rw [Cyclotomic.bcrisFrobenius_algebraMap, bcrisPlusFrobenius_padicField]
  rfl

/-- Actual crystalline Frobenius is Q_p-linear. -/
def bcrisFrobeniusAlg : PeriodRing.Bcris p →ₐ[ℚ_[p]] PeriodRing.Bcris p :=
  { Cyclotomic.bcrisFrobenius p with commutes' := bcrisFrobenius_padicField p }

/-- The actual fixed-scalar algebra for a subgroup of the absolute Galois group. -/
def fixedScalars (H : Subgroup (PeriodRing.PadicGalois p)) : Subalgebra ℚ_[p] (PeriodRing.Bcris p) :=
  fixedSubalgebra ((TateCyclotomic.Galois.galoisBcrisAction p).comp H.subtype)

theorem mem_fixedScalars (H : Subgroup (PeriodRing.PadicGalois p)) (a : PeriodRing.Bcris p) :
    a ∈ fixedScalars p H ↔ ∀ σ : H, TateCyclotomic.Galois.galoisBcrisAction p σ a = a := Iff.rfl

theorem fixedScalars_nontrivial (H : Subgroup (PeriodRing.PadicGalois p)) : Nontrivial (fixedScalars p H) :=
  inferInstance

theorem frobenius_mem_fixedScalars (H : Subgroup (PeriodRing.PadicGalois p))
    (a : fixedScalars p H) : Cyclotomic.bcrisFrobenius p a ∈ fixedScalars p H :=
  map_mem_fixedSubalgebra ((TateCyclotomic.Galois.galoisBcrisAction p).comp H.subtype) (bcrisFrobeniusAlg p)
    (fun σ b => TateCyclotomic.Galois.galoisBcrisAction_frobenius p σ b) a

/-- The Frobenius endomorphism of the actual fixed-scalar algebra. -/
def fixedScalarsFrobenius (H : Subgroup (PeriodRing.PadicGalois p)) : fixedScalars p H →ₐ[ℚ_[p]] fixedScalars p H :=
  fixedSubalgebraMap ((TateCyclotomic.Galois.galoisBcrisAction p).comp H.subtype) (bcrisFrobeniusAlg p)
    (fun σ b => TateCyclotomic.Galois.galoisBcrisAction_frobenius p σ b)

end

/-!
# The local absolute Galois group acting on the actual period ring

An algebraic closure of a finite extension K/Q_p is also an algebraic closure
of Q_p. Conjugation identifies its K-automorphisms with the subgroup fixing the
chosen image of K inside the fixed algebraic closure used by the period rings.
-/

section Conjugation

variable (F : Type*) {K L M : Type*} [Field F] [Field K] [Field L] [Field M]
  [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L] [Algebra F M]

def restrictScalarAut : (L ≃ₐ[K] L) →* (L ≃ₐ[F] L) where
  toFun σ := σ.restrictScalars F
  map_one' := by ext; rfl
  map_mul' σ τ := by ext; rfl

variable (e : L ≃ₐ[F] M)

def conjugateRestriction : (L ≃ₐ[K] L) →* (M ≃ₐ[F] M) :=
  (AlgEquiv.autCongr e).toMonoidHom.comp (restrictScalarAut F)

theorem conjugateRestriction_apply (σ : L ≃ₐ[K] L) (x : M) :
    conjugateRestriction (K := K) F e σ x = e (σ (e.symm x)) := rfl

def baseEmbedding : K →ₐ[F] M := e.toAlgHom.comp (IsScalarTower.toAlgHom F K L)

theorem conjugateRestriction_fixes_base (σ : L ≃ₐ[K] L) (a : K) :
    conjugateRestriction (K := K) F e σ (baseEmbedding (K := K) F e a) = baseEmbedding (K := K) F e a := by
  change e (σ (e.symm (e (algebraMap K L a)))) = e (algebraMap K L a)
  rw [e.symm_apply_apply, σ.commutes]

theorem conjugateRestriction_injective : Function.Injective (conjugateRestriction (K := K) F e) := by
  intro σ τ h
  apply AlgEquiv.ext
  intro x
  apply e.injective
  have he := congrArg (fun g : M ≃ₐ[F] M => g (e x)) h
  simpa only [conjugateRestriction_apply, AlgEquiv.symm_apply_apply] using he

/-- The image consists exactly of automorphisms fixing the embedded base field. -/
theorem conjugateRestriction_range : (conjugateRestriction (K := K) F e).range =
    (baseEmbedding (K := K) F e).fieldRange.fixingSubgroup := by
  apply le_antisymm
  · intro σ hσ
    obtain ⟨τ, rfl⟩ := hσ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := (AlgHom.mem_fieldRange (f := baseEmbedding (K := K) F e)).mp hx
    exact conjugateRestriction_fixes_base F e τ a
  · intro σ hσ
    have hs : ∀ a : K, σ (baseEmbedding (K := K) F e a) = baseEmbedding (K := K) F e a := by
      intro a
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ ⟨a, rfl⟩
    let τ : L ≃ₐ[K] L :=
      { e.toRingEquiv.trans (σ.toRingEquiv.trans e.symm.toRingEquiv) with
        commutes' a := by
          change e.symm (σ (e (algebraMap K L a))) = algebraMap K L a
          have ha := congrArg e.symm (hs a)
          exact ha.trans (e.symm_apply_apply (algebraMap K L a)) }
    refine ⟨τ, ?_⟩
    apply AlgEquiv.ext
    intro x
    change e (e.symm (σ (e (e.symm x)))) = σ x
    rw [e.apply_symm_apply, e.apply_symm_apply]

end Conjugation

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.Galois

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

/-- An actual isomorphism of algebraic closures over Q_p. -/
def closureEquiv : AlgebraicClosure K ≃ₐ[ℚ_[p]] PadicAlgCl p :=
  IsAlgClosure.equiv ℚ_[p] (AlgebraicClosure K) (PadicAlgCl p)

abbrev LocalGalois := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K

def galoisToPadic : LocalGalois K →* PeriodRing.PadicGalois p :=
  conjugateRestriction ℚ_[p] (closureEquiv p K)

def fieldEmbedding : K →ₐ[ℚ_[p]] PadicAlgCl p := baseEmbedding ℚ_[p] (closureEquiv p K)

theorem galoisToPadic_injective : Function.Injective (galoisToPadic p K) :=
  conjugateRestriction_injective ℚ_[p] (closureEquiv p K)

theorem galoisToPadic_range : (galoisToPadic p K).range = (fieldEmbedding p K).fieldRange.fixingSubgroup :=
  conjugateRestriction_range ℚ_[p] (closureEquiv p K)

/-- The actual local absolute Galois action on B_cris. -/
def localPeriodAction : LocalGalois K →* (PeriodRing.Bcris p ≃ₐ[ℚ_[p]] PeriodRing.Bcris p) :=
  (TateCyclotomic.Galois.galoisBcrisAction p).comp (galoisToPadic p K)

def localFixedScalars : Subalgebra ℚ_[p] (PeriodRing.Bcris p) := fixedSubalgebra (localPeriodAction p K)

theorem localPeriodAction_frobenius (σ : LocalGalois K) (x : PeriodRing.Bcris p) :
    localPeriodAction p K σ (Cyclotomic.bcrisFrobenius p x) =
      Cyclotomic.bcrisFrobenius p (localPeriodAction p K σ x) :=
  TateCyclotomic.Galois.galoisBcrisAction_frobenius p (galoisToPadic p K σ) x

def localScalarFrobenius : localFixedScalars p K →ₐ[ℚ_[p]] localFixedScalars p K :=
  fixedSubalgebraMap (localPeriodAction p K) (bcrisFrobeniusAlg p)
    (localPeriodAction_frobenius p K)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineScalars
