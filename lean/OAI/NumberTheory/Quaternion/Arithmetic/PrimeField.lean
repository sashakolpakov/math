import OAI.NumberTheory.Quaternion.Arithmetic.RationalNormComparison
import Mathlib.Topology.Algebra.UniformRing

/-! # Prime Field -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PrimeField

noncomputable section

section

/-! The rational prime fields inside completions of the same residue
characteristic are uniformly isomorphic. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

def primeFieldRatEquiv (K : Type*) [Field K] [CharZero K] : ℚ ≃+* (⊥ : Subfield K) :=
  RingEquiv.ofBijective (Rat.castHom (⊥ : Subfield K))
    ⟨Rat.cast_injective, by
      intro x
      have hx := x.property
      change x.val ∈ ((⊥ : Subfield K) : Set K) at hx
      rw [PrimeLocalIntegral.bot_subfield_coe_eq_ratRange] at hx
      obtain ⟨q, hq⟩ := hx
      exact ⟨q, Subtype.ext hq⟩⟩

@[simp] theorem primeFieldRatEquiv_apply (K : Type*) [Field K] [CharZero K] (q : ℚ) :
    primeFieldRatEquiv K q = (q : (⊥ : Subfield K)) := rfl

variable {F : Type} [Field F] [NumberField F]

local instance primeFieldUniformityCharZero (v : HeightOneSpectrum (𝓞 F)) :
    CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F _

def rationalPrimeFieldEquiv (v w : HeightOneSpectrum (𝓞 F)) :
    (⊥ : Subfield (v.adicCompletion F)) ≃+* (⊥ : Subfield (w.adicCompletion F)) :=
  (primeFieldRatEquiv (v.adicCompletion F)).symm.trans (primeFieldRatEquiv (w.adicCompletion F))

theorem rationalPrimeFieldEquiv_continuousAt_zero (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) :
    ContinuousAt (rationalPrimeFieldEquiv v w) 0 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε
    ((LocalCompletion.natCast_norm_lt_one_iff w _).mpr dvd_rfl)
  refine ⟨‖(LocalCompletion.residuePrime v : v.adicCompletion F)‖ ^ j,
    pow_pos (LocalCompletion.residuePrime_norm_pos v) _, ?_⟩
  intro x hx
  obtain ⟨q, rfl⟩ := (primeFieldRatEquiv (v.adicCompletion F)).surjective x
  simp only [primeFieldRatEquiv_apply, dist_zero_right] at hx
  change ‖(q : v.adicCompletion F)‖ < ‖(LocalCompletion.residuePrime v : v.adicCompletion F)‖ ^ j at hx
  rw [primeFieldRatEquiv_apply, map_ratCast, map_zero, dist_zero_right]
  change ‖(q : w.adicCompletion F)‖ < ε
  have hq : ‖(q : v.adicCompletion F)‖ ≤
      ‖(((LocalCompletion.residuePrime v : ℚ) ^ j : ℚ) : v.adicCompletion F)‖ := by
    simpa only [Rat.cast_pow, Rat.cast_natCast, norm_pow] using hx.le
  have hw := (RationalNormComparison.ratCast_norm_le_iff_same_residuePrime v w hvw q ((LocalCompletion.residuePrime v : ℚ) ^ j)).mp hq
  have hw' : ‖(q : w.adicCompletion F)‖ ≤ ‖(LocalCompletion.residuePrime w : w.adicCompletion F)‖ ^ j := by
    simpa only [Rat.cast_pow, Rat.cast_natCast, norm_pow, hvw] using hw
  exact hw'.trans_lt hj

theorem rationalPrimeFieldEquiv_uniformContinuous (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) : UniformContinuous (rationalPrimeFieldEquiv v w) :=
  uniformContinuous_of_continuousAt_zero (rationalPrimeFieldEquiv v w).toAddMonoidHom
    (rationalPrimeFieldEquiv_continuousAt_zero v w hvw)

def rationalPrimeFieldUniformEquiv (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) :
    (⊥ : Subfield (v.adicCompletion F)) ≃ᵤ (⊥ : Subfield (w.adicCompletion F)) where
  toEquiv := (rationalPrimeFieldEquiv v w).toEquiv
  uniformContinuous_toFun := rationalPrimeFieldEquiv_uniformContinuous v w hvw
  uniformContinuous_invFun := rationalPrimeFieldEquiv_uniformContinuous w v hvw.symm

end

section

/-! Closed prime subfields at places of the same residue characteristic
are canonically isomorphic as topological fields. The map extends the
rational prime-field isomorphism by completeness. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F]

local instance primeFieldComparisonCharZero (v : HeightOneSpectrum (𝓞 F)) :
    CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F _

def primeFieldCompletionInclusion (v : HeightOneSpectrum (𝓞 F)) :
    (⊥ : Subfield (v.adicCompletion F)) →+* TangentBracket.closedPrimeSubfield (v.adicCompletion F) :=
  Subfield.inclusion bot_le

theorem primeFieldCompletionInclusion_isUniformInducing (v : HeightOneSpectrum (𝓞 F)) :
    IsUniformInducing (primeFieldCompletionInclusion v) := by
  let h : (⊥ : Subfield (v.adicCompletion F)) ≤ TangentBracket.closedPrimeSubfield (v.adicCompletion F) := bot_le
  exact (isUniformEmbedding_set_inclusion h).isUniformInducing

theorem primeFieldCompletionInclusion_dense (v : HeightOneSpectrum (𝓞 F)) :
    DenseRange (primeFieldCompletionInclusion v) := by
  let h : (⊥ : Subfield (v.adicCompletion F)) ≤ TangentBracket.closedPrimeSubfield (v.adicCompletion F) := bot_le
  change DenseRange (Set.inclusion h)
  exact (denseRange_inclusion_iff h).mpr Subset.rfl

def primeFieldTargetHom (v w : HeightOneSpectrum (𝓞 F)) :
    (⊥ : Subfield (v.adicCompletion F)) →+* TangentBracket.closedPrimeSubfield (w.adicCompletion F) :=
  (primeFieldCompletionInclusion w).comp (rationalPrimeFieldEquiv v w).toRingHom

theorem primeFieldTargetHom_uniformContinuous (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) : UniformContinuous (primeFieldTargetHom v w) :=
  (primeFieldCompletionInclusion_isUniformInducing w).uniformContinuous.comp
    (rationalPrimeFieldEquiv_uniformContinuous v w hvw)

def closedPrimeFieldMap (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) :
    TangentBracket.closedPrimeSubfield (v.adicCompletion F) →+* TangentBracket.closedPrimeSubfield (w.adicCompletion F) :=
  IsDenseInducing.extendRingHom (primeFieldCompletionInclusion_isUniformInducing v)
    (primeFieldCompletionInclusion_dense v) (primeFieldTargetHom_uniformContinuous v w hvw)

theorem closedPrimeFieldMap_uniformContinuous (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) : UniformContinuous (closedPrimeFieldMap v w hvw) :=
  uniformContinuous_uniformly_extend (primeFieldCompletionInclusion_isUniformInducing v)
    (primeFieldCompletionInclusion_dense v) (primeFieldTargetHom_uniformContinuous v w hvw)

theorem closedPrimeFieldMap_inclusion (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) (a : (⊥ : Subfield (v.adicCompletion F))) :
    closedPrimeFieldMap v w hvw (primeFieldCompletionInclusion v a) =
      primeFieldCompletionInclusion w (rationalPrimeFieldEquiv v w a) :=
  IsDenseInducing.extend_eq
    ((primeFieldCompletionInclusion_isUniformInducing v).isDenseInducing
      (primeFieldCompletionInclusion_dense v))
    (primeFieldTargetHom_uniformContinuous v w hvw).continuous a

theorem closedPrimeFieldMap_inverse (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) (x : TangentBracket.closedPrimeSubfield (v.adicCompletion F)) :
    closedPrimeFieldMap w v hvw.symm (closedPrimeFieldMap v w hvw x) = x := by
  have he : (fun y => closedPrimeFieldMap w v hvw.symm (closedPrimeFieldMap v w hvw y)) = id := by
    apply (primeFieldCompletionInclusion_dense v).equalizer
      ((closedPrimeFieldMap_uniformContinuous w v hvw.symm).continuous.comp
        (closedPrimeFieldMap_uniformContinuous v w hvw).continuous) continuous_id
    funext a
    simp only [Function.comp_def, closedPrimeFieldMap_inclusion, id_eq]
    congr 1
    exact (rationalPrimeFieldEquiv v w).left_inv a
  exact congrFun he x

def closedPrimeFieldRingEquiv (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) :
    TangentBracket.closedPrimeSubfield (v.adicCompletion F) ≃+* TangentBracket.closedPrimeSubfield (w.adicCompletion F) :=
  { closedPrimeFieldMap v w hvw with
    invFun := closedPrimeFieldMap w v hvw.symm
    left_inv := closedPrimeFieldMap_inverse v w hvw
    right_inv := closedPrimeFieldMap_inverse w v hvw.symm }

def closedPrimeFieldUniformEquiv (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) :
    TangentBracket.closedPrimeSubfield (v.adicCompletion F) ≃ᵤ TangentBracket.closedPrimeSubfield (w.adicCompletion F) where
  toEquiv := (closedPrimeFieldRingEquiv v w hvw).toEquiv
  uniformContinuous_toFun := closedPrimeFieldMap_uniformContinuous v w hvw
  uniformContinuous_invFun := closedPrimeFieldMap_uniformContinuous w v hvw.symm

end

/-! Every completion in a residue-prime block is a finite-dimensional
topological algebra over one chosen closed prime subfield. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

def primeBlockScalarMap (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) :
    TangentBracket.closedPrimeSubfield (v.adicCompletion F) →+* w.adicCompletion F :=
  (TangentBracket.closedPrimeSubfield (w.adicCompletion F)).subtype.comp (closedPrimeFieldMap v w hvw)

theorem primeBlockScalarMap_continuous (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) : Continuous (primeBlockScalarMap v w hvw) :=
  continuous_subtype_val.comp (closedPrimeFieldMap_uniformContinuous v w hvw).continuous

@[instance_reducible]
def primeBlockScalarAlgebra (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) :
    Algebra (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (w.adicCompletion F) :=
  (primeBlockScalarMap v w hvw).toAlgebra

theorem primeBlockScalar_continuousSMul (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) :
    letI := primeBlockScalarAlgebra v w hvw
    ContinuousSMul (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (w.adicCompletion F) := by
  let : Algebra (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (w.adicCompletion F) :=
    primeBlockScalarAlgebra v w hvw
  exact ⟨((primeBlockScalarMap_continuous v w hvw).comp continuous_fst).mul continuous_snd⟩

theorem primeBlockScalar_finiteDimensional (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) :
    letI := primeBlockScalarAlgebra v w hvw
    FiniteDimensional (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (w.adicCompletion F) := by
  let : Algebra (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (w.adicCompletion F) :=
    primeBlockScalarAlgebra v w hvw
  let κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F)
  let κw := TangentBracket.closedPrimeSubfield (w.adicCompletion F)
  let : Algebra κ κw := (closedPrimeFieldMap v w hvw).toAlgebra
  let : IsScalarTower κ κw (w.adicCompletion F) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : FiniteDimensional κ κw := Module.Finite.of_surjective (Algebra.linearMap κ κw)
    (closedPrimeFieldRingEquiv v w hvw).surjective
  let : FiniteDimensional κw (w.adicCompletion F) := LocalCompletion.finiteCompletion_finiteDimensional_closedPrime w
  exact Module.Finite.trans κw (w.adicCompletion F)

end

end OAI.NumberTheory.Quaternion.Arithmetic.PrimeField
