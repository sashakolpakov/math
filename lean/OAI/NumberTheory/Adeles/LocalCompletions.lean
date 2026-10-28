import Mathlib

/-! # Local Completions -/

namespace OAI.NumberTheory.Adeles.LocalCompletions.CompletionFactors

noncomputable section

section

/-! The absolute idele modulus, constructed from normalized local absolute values. -/

open _root_.NumberField IsDedekindDomain
open scoped _root_.NumberField _root_.Topology NNReal

abbrev Adele (K : Type*) [Field K] [NumberField K] := AdeleRing (𝓞 K) K
abbrev FiniteAdele (K : Type*) [Field K] [NumberField K] := FiniteAdeleRing (𝓞 K) K
abbrev Idele (K : Type*) [Field K] [NumberField K] := (Adele K)ˣ

def principalIdele (K : Type*) [Field K] [NumberField K] : Kˣ →* Idele K :=
  Units.map (algebraMap K (Adele K)).toMonoidHom

abbrev IdeleClass (K : Type*) [Field K] [NumberField K] :=
  Idele K ⧸ (principalIdele K).range

variable {K : Type*} [Field K] [NumberField K]

/-- Only finitely many normalized finite-place factors differ from one. -/
theorem finite_norm_support (a : (FiniteAdele K)ˣ) :
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 K) => ‖a.val v‖₊) := by
  have h := FiniteAdeleRing.unitsEquiv_finite_valued_eq_one a
  have hnorm : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ‖a.val v‖₊ = 1 := by
    filter_upwards [h] with v hv
    apply NNReal.eq
    change ‖a.val v‖ = 1
    rw [FinitePlace.norm_def]
    change ((WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v))
      (Valued.v (a.val v)) : ℝ) = 1
    change Valued.v (a.val v) = 1 at hv
    simp [hv]
  exact hnorm

/-- The finite part of the absolute modulus. -/
def finiteModulus : (FiniteAdele K)ˣ →* ℝ≥0 where
  toFun a := ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.val v‖₊
  map_one' := by
    change (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(1 : v.adicCompletion K)‖₊) = 1
    simp
  map_mul' a b := by
    change (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.val v * b.val v‖₊) = _
    simp only [nnnorm_mul]
    exact finprod_mul_distrib (finite_norm_support a) (finite_norm_support b)

def infiniteModulus : (InfiniteAdeleRing K)ˣ →* ℝ≥0 where
  toFun a := ∏ v : InfinitePlace K, ‖a.val v‖₊ ^ v.mult
  map_one' := by
    change (∏ v : InfinitePlace K, ‖(1 : v.Completion)‖₊ ^ v.mult) = 1
    simp
  map_mul' a b := by
    change (∏ v : InfinitePlace K, ‖a.val v * b.val v‖₊ ^ v.mult) = _
    simp only [nnnorm_mul, mul_pow, Finset.prod_mul_distrib]

theorem finiteModulus_eq_one_of_integral
    (a : (FiniteAdele K)ˣ)
    (ha : ∀ v : HeightOneSpectrum (𝓞 K), a.val v ∈ v.adicCompletionIntegers K)
    (hi : ∀ v : HeightOneSpectrum (𝓞 K), a.inv v ∈ v.adicCompletionIntegers K) :
    finiteModulus a = 1 := by
  apply finprod_eq_one_of_forall_eq_one
  intro v
  have hv : Valued.v (a.val v) = 1 :=
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := RestrictedProduct.unitsEquiv _ a v)).mp ⟨ha v, hi v⟩
  apply NNReal.eq
  change ‖a.val v‖ = 1
  rw [FinitePlace.norm_def]
  simp [hv]

theorem continuous_finiteModulus : Continuous (finiteModulus (K := K)) := by
  apply continuous_of_continuousAt_one
  have ho : IsOpen {a : FiniteAdele K |
      ∀ v : HeightOneSpectrum (𝓞 K), a v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem
      (fun v : HeightOneSpectrum (𝓞 K) => Valued.isOpen_valuationSubring (v.adicCompletion K))
  have hv := ho.preimage (Units.continuous_val (M := FiniteAdele K))
  have hi := ho.preimage (Units.continuous_coe_inv (M := FiniteAdele K))
  apply continuousAt_const.congr_of_eventuallyEq
  filter_upwards [(hv.inter hi).mem_nhds (show (1 : (FiniteAdele K)ˣ) ∈ _ from
    ⟨fun v => (v.adicCompletionIntegers K).one_mem,
      fun v => (v.adicCompletionIntegers K).one_mem⟩)] with a ha
  exact finiteModulus_eq_one_of_integral a ha.1 ha.2

theorem continuous_infiniteModulus : Continuous (infiniteModulus (K := K)) := by
  apply continuous_finsetProd
  intro v _
  have he : Continuous (fun a : InfiniteAdeleRing K => a v) := continuous_apply v
  exact (he.comp (Units.continuous_val (M := InfiniteAdeleRing K))).nnnorm.pow v.mult

def finiteIdeleProjection : Idele K →* (FiniteAdele K)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdele K))

def infiniteIdeleProjection : Idele K →* (InfiniteAdeleRing K)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdele K))

/-- The full product of normalized local absolute values. -/
def ideleModulusNonneg : Idele K →* ℝ≥0 :=
  (infiniteModulus.comp infiniteIdeleProjection) *
    (finiteModulus.comp finiteIdeleProjection)

theorem continuous_ideleModulusNonneg : Continuous (ideleModulusNonneg (K := K)) := by
  apply Continuous.mul
  · exact continuous_infiniteModulus.comp (Continuous.units_map _ continuous_fst)
  · exact continuous_finiteModulus.comp (Continuous.units_map _ continuous_snd)

theorem infiniteModulus_principal (x : Kˣ) :
    (infiniteModulus (infiniteIdeleProjection (principalIdele K x)) : ℝ) =
      |Algebra.norm ℚ (x : K)| := by
  change ((∏ v : InfinitePlace K,
    ‖(algebraMap K (InfiniteAdeleRing K) (x : K)) v‖₊ ^ v.mult : ℝ≥0) : ℝ) = _
  simp only [NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm]
  exact InfiniteAdeleRing.coe_norm_eq_abs_norm (x : K)

theorem finiteModulus_principal (x : Kˣ) :
    (finiteModulus (finiteIdeleProjection (principalIdele K x)) : ℝ) =
      |Algebra.norm ℚ (x : K)|⁻¹ := by
  change ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
    ‖FinitePlace.embedding v (x : K)‖₊ : ℝ≥0) : ℝ) = _
  have hcast := NNReal.toRealHom.toMonoidHom.map_finprod_of_injective
    NNReal.coe_injective (fun v : HeightOneSpectrum (𝓞 K) => ‖FinitePlace.embedding v (x : K)‖₊)
  change ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
    ‖FinitePlace.embedding v (x : K)‖₊ : ℝ≥0) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖FinitePlace.embedding v (x : K)‖ at hcast
  rw [hcast]
  change (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖FinitePlace.embedding v (x : K)‖) = _
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum]
  change (∏ᶠ v : FinitePlace K, ‖FinitePlace.embedding v.maximalIdeal (x : K)‖) = _
  simp_rw [FinitePlace.norm_embedding_eq]
  exact FinitePlace.prod_eq_inv_abs_norm (Units.ne_zero x)

/-- The actual product formula kills the diagonal multiplicative group. -/
theorem ideleModulusNonneg_principal (x : Kˣ) :
    ideleModulusNonneg (principalIdele K x) = 1 := by
  apply NNReal.eq
  change (infiniteModulus (infiniteIdeleProjection (principalIdele K x)) : ℝ) *
    (finiteModulus (finiteIdeleProjection (principalIdele K x)) : ℝ) = 1
  rw [infiniteModulus_principal, finiteModulus_principal]
  have hn : Algebra.norm ℚ (x : K) ≠ 0 := Algebra.norm_ne_zero_iff.mpr (Units.ne_zero x)
  have hnR : (Algebra.norm ℚ (x : K) : ℝ) ≠ 0 := by exact_mod_cast hn
  simpa only [Rat.cast_abs, Rat.cast_inv] using mul_inv_cancel₀ (abs_ne_zero.mpr hnR)

/-- Nonnegative units are the multiplicative group of positive real numbers. -/
def ideleModulus : Idele K →ₜ* ℝ≥0ˣ where
  toMonoidHom := ideleModulusNonneg.toHomUnits
  continuous_toFun := Units.continuous_iff.mpr
    ⟨continuous_ideleModulusNonneg, continuous_ideleModulusNonneg.comp continuous_inv⟩

theorem ideleModulus_principal (x : Kˣ) : ideleModulus (principalIdele K x) = 1 := by
  apply Units.ext
  exact ideleModulusNonneg_principal x

/-- The absolute modulus descends to the concrete quotient by principal ideles. -/
def ideleClassModulus : IdeleClass K →ₜ* ℝ≥0ˣ where
  toMonoidHom := QuotientGroup.lift (principalIdele K).range ideleModulus.toMonoidHom (by
    rintro a ⟨x, rfl⟩
    exact ideleModulus_principal x)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk (principalIdele K).range).continuous_iff.mpr
    ideleModulus.continuous

@[simp] theorem ideleClassModulus_mk (a : Idele K) :
    ideleClassModulus (QuotientGroup.mk a) = ideleModulus a := rfl

/-- The descended map computes the prescribed normalized product on representatives. -/
theorem ideleClassModulus_mk_formula (a : Idele K) :
    (ideleClassModulus (QuotientGroup.mk a) : ℝ≥0) =
      (∏ v : InfinitePlace K, ‖a.val.1 v‖₊ ^ v.mult) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.val.2 v‖₊ := rfl

theorem ideleModulus_principal_mul (x : Kˣ) (a : Idele K) :
    ideleModulus (principalIdele K x * a) = ideleModulus a := by
  rw [map_mul, ideleModulus_principal, one_mul]

/-- Norm-one ideles, defined by the constructed absolute modulus. -/
def normOneIdeles (K : Type*) [Field K] [NumberField K] : Subgroup (Idele K) :=
  (ideleModulus (K := K)).toMonoidHom.ker

/-- Norm-one idele classes, with the inherited topology. -/
def normOneIdeleClasses (K : Type*) [Field K] [NumberField K] : Subgroup (IdeleClass K) :=
  (ideleClassModulus (K := K)).toMonoidHom.ker

/-- The product formula places the diagonal group inside the norm-one ideles. -/
def principalNormOne : Kˣ →* normOneIdeles K :=
  (principalIdele K).codRestrict (normOneIdeles K) ideleModulus_principal

end

/-! Canonical extension maps between completions at finite places. -/

open _root_.NumberField IsDedekindDomain HeightOneSpectrum
open scoped _root_.NumberField _root_.Topology

variable {F E : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- Extension of the field embedding to the completions at `w | v`. -/
def finiteCompletionMap : v.adicCompletion F →+* w.adicCompletion E :=
  ((adicCompletion.equiv E w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation F)) (WithVal (w.valuation E)))
      (uniformContinuous_algebraMap_liesOver (K := F) (L := E) v w).continuous)).comp
        (adicCompletion.equiv F v).toRingHom

theorem continuous_finiteCompletionMap : Continuous (finiteCompletionMap v w) :=
  (adicCompletion.continuous_ofCompletion E w).comp
    (UniformSpace.Completion.continuous_map.comp
      (adicCompletion.continuous_toCompletion F v))

@[simp] theorem finiteCompletionMap_coe (x : F) :
    finiteCompletionMap v w (x : v.adicCompletion F) =
      (algebraMap F E x : w.adicCompletion E) := by
  apply adicCompletion.ext
  change UniformSpace.Completion.mapRingHom
    (algebraMap (WithVal (v.valuation F)) (WithVal (w.valuation E))) _
      ((WithVal.equiv (v.valuation F)).symm x : UniformSpace.Completion _) = _
  rw [UniformSpace.Completion.mapRingHom_coe]
  rfl

namespace FiniteLiesOver

/-- Scoped to avoid a second algebra structure when the two fields coincide. -/
scoped instance : Algebra (v.adicCompletion F) (w.adicCompletion E) :=
  (finiteCompletionMap v w).toAlgebra

scoped instance : IsScalarTower F (v.adicCompletion F) (w.adicCompletion E) :=
  .of_algebraMap_eq fun x => (finiteCompletionMap_coe v w x).symm

scoped instance : ContinuousSMul (v.adicCompletion F) (w.adicCompletion E) where
  continuous_smul :=
    ((continuous_finiteCompletionMap v w).comp continuous_fst).mul continuous_snd

end FiniteLiesOver

open scoped OAI.NumberTheory.Adeles.LocalCompletions.CompletionFactors.FiniteLiesOver

/-- The completion extension is finite-dimensional, using density and finite-dimensional closure. -/
theorem finiteCompletion_finiteDimensional :
    FiniteDimensional (v.adicCompletion F) (w.adicCompletion E) := inferInstance

end

end OAI.NumberTheory.Adeles.LocalCompletions.CompletionFactors
