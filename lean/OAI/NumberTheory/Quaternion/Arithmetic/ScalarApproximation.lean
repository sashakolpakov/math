import OAI.NumberTheory.Adeles.LocalDensity

/-! # Scalar Approximation -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ScalarApproximation

noncomputable section

section

/-! Simultaneous integral approximation in finite completions of an arbitrary
number field. The approximation is constructed by the ideal Chinese remainder
theorem after choosing local prime-power precision. -/

open scoped Classical _root_.NumberField _root_.Topology WithZero
open _root_.NumberField IsDedekindDomain HeightOneSpectrum

variable {F : Type*} [Field F] [NumberField F]

theorem idealPower_residue_subset_open
    (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F)
    (U : Set (v.adicCompletion F)) (hU : IsOpen U)
    (ha : algebraMap (𝓞 F) (v.adicCompletion F) a ∈ U) :
    ∃ k : ℕ, ∀ b : 𝓞 F, b - a ∈ v.asIdeal ^ k →
      algebraMap (𝓞 F) (v.adicCompletion F) b ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp (hU.mem_nhds ha)
  let δ : (ℤᵐ⁰)ˣ := Units.map
    (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := .ofClass (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰))).toMonoidHom γ
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt (Units.ne_zero δ)
  refine ⟨k, fun b hb => hγ ?_⟩
  change Valued.v.restrict (algebraMap (𝓞 F) (v.adicCompletion F) b -
    algebraMap (𝓞 F) (v.adicCompletion F) a) < γ.val
  rw [Valuation.restrict_lt_iff_lt_embedding, ← map_sub]
  change Valued.v (((b - a : 𝓞 F) : F) : v.adicCompletion F) < _
  rw [adicCompletion.valued_coe, valuation_of_algebraMap]
  exact ((v.intValuation_le_pow_iff_mem (b - a) k).mpr hb).trans_lt hk

/-- Independent prescribed open conditions on finitely many local integers
have a simultaneous global algebraic-integer solution. -/
theorem simultaneous_integral_approximation
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (U : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F))
    (hU : ∀ v ∈ T, IsOpen (U v))
    (hn : ∀ v ∈ T, ∃ x ∈ U v, x ∈ v.adicCompletionIntegers F) :
    ∃ a : 𝓞 F, ∀ v ∈ T, algebraMap (𝓞 F) (v.adicCompletion F) a ∈ U v := by
  have hrep : ∀ v : T, ∃ a : 𝓞 F,
      algebraMap (𝓞 F) (v.val.adicCompletion F) a ∈ U v.val := by
    intro v
    obtain ⟨x, hx, hint⟩ := hn v.val v.property
    have hc := Adeles.LocalDensity.CompletionFactors.local_integer_mem_closure v.val x hint
    obtain ⟨y, hy, a, rfl⟩ := mem_closure_iff.mp hc (U v.val) (hU v.val v.property) hx
    exact ⟨a, hy⟩
  choose a ha using hrep
  choose k hk using fun v : T => idealPower_residue_subset_open v.val (a v)
    (U v.val) (hU v.val v.property) (ha v)
  let I : T → Ideal (𝓞 F) := fun v => v.val.asIdeal ^ k v
  have hcop : Pairwise (fun v w : T => IsCoprime (I v) (I w)) := by
    intro v w hvw
    exact v.val.isCoprime_pow_of_ne w.val (fun h => hvw (Subtype.ext h)) (k v) (k w)
  obtain ⟨b, hb⟩ := Ideal.pi_quotient_surjective hcop
    (fun v : T => Ideal.Quotient.mk (I v) (a v))
  refine ⟨b, ?_⟩
  intro v hv
  apply hk ⟨v, hv⟩ b
  apply Ideal.Quotient.eq.mp
  exact hb ⟨v, hv⟩

end

section

/-! Additive strong approximation for number fields, proved from integral
Chinese remainder approximation and a common denominator for each adele. -/

open scoped Classical _root_.NumberField RestrictedProduct
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (F : Type*) [Field F] [NumberField F]

abbrev ScalarFiniteAdeles := FiniteAdeleRing (𝓞 F) F

def integralScalarAdeles : Subring (ScalarFiniteAdeles F) where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}
  zero_mem' v := (v.adicCompletionIntegers F).zero_mem
  one_mem' v := (v.adicCompletionIntegers F).one_mem
  add_mem' ha hb v := (v.adicCompletionIntegers F).toSubring.add_mem (ha v) (hb v)
  mul_mem' ha hb v := (v.adicCompletionIntegers F).toSubring.mul_mem (ha v) (hb v)
  neg_mem' ha v := (v.adicCompletionIntegers F).toSubring.neg_mem (ha v)

theorem algebraMap_mem_integralScalarAdeles (a : 𝓞 F) :
    algebraMap (𝓞 F) (ScalarFiniteAdeles F) a ∈ integralScalarAdeles F := by
  intro v
  exact coe_mem_adicCompletionIntegers (K := F) v a

def integralScalarEmbedding : 𝓞 F →+* integralScalarAdeles F :=
  (algebraMap (𝓞 F) (ScalarFiniteAdeles F)).codRestrict (integralScalarAdeles F)
    (algebraMap_mem_integralScalarAdeles F)

def integralScalarProductHomeomorph :
    ((v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F) ≃ₜ integralScalarAdeles F :=
  (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).toHomeomorph.trans
      (Homeomorph.setCongr (by rw [RestrictedProduct.range_structureMap]; rfl))

@[simp] theorem integralScalarProductHomeomorph_embedding (a : 𝓞 F) :
    integralScalarProductHomeomorph F
      (fun v => algebraMap (𝓞 F) (v.adicCompletionIntegers F) a) =
      integralScalarEmbedding F a := rfl

theorem denseRange_integralScalarProduct :
    DenseRange (fun a : 𝓞 F => fun v : HeightOneSpectrum (𝓞 F) =>
      algebraMap (𝓞 F) (v.adicCompletionIntegers F) a) := by
  intro x
  rw [mem_closure_iff]
  intro V hV hx
  obtain ⟨T, U, hU, hsub⟩ := isOpen_pi_iff.mp hV x hx
  let W : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F) :=
    fun v => Subtype.val '' U v
  have ho : ∀ v ∈ T, IsOpen (W v) := by
    intro v hv
    exact (Valued.isOpen_valuationSubring (v.adicCompletion F)).isOpenMap_subtype_val
      _ (hU v hv).1
  have hn : ∀ v ∈ T, ∃ y ∈ W v, y ∈ v.adicCompletionIntegers F := by
    intro v hv
    exact ⟨(x v).val, ⟨x v, (hU v hv).2, rfl⟩, (x v).property⟩
  obtain ⟨a, ha⟩ := simultaneous_integral_approximation T W ho hn
  refine ⟨(fun v => algebraMap (𝓞 F) (v.adicCompletionIntegers F) a), hsub ?_,
    Set.mem_range_self a⟩
  intro v hv
  obtain ⟨y, hy, heq⟩ := ha v hv
  have he : y = algebraMap (𝓞 F) (v.adicCompletionIntegers F) a := Subtype.ext heq
  change algebraMap (𝓞 F) (v.adicCompletionIntegers F) a ∈ U v
  exact he ▸ hy

theorem denseRange_integralScalarEmbedding : DenseRange (integralScalarEmbedding F) := by
  have h := (integralScalarProductHomeomorph F).surjective.denseRange.comp
    (denseRange_integralScalarProduct F) (integralScalarProductHomeomorph F).continuous
  simpa only [Function.comp_def, integralScalarProductHomeomorph_embedding] using h

/-- A single nonzero algebraic integer clears all finite-adelic denominators. -/
theorem exists_integralScalar_multiple (a : ScalarFiniteAdeles F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧
      algebraMap (𝓞 F) (ScalarFiniteAdeles F) d * a ∈ integralScalarAdeles F := by
  have hfinite : {v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp a.property
  choose d hd hda using fun v : HeightOneSpectrum (𝓞 F) =>
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
  let n : 𝓞 F := ∏ v ∈ hfinite.toFinset, d v
  refine ⟨n, Finset.prod_ne_zero_iff.mpr (fun v _ => nonZeroDivisors.ne_zero (hd v)), ?_⟩
  intro v
  change algebraMap (𝓞 F) (v.adicCompletion F) n * a v ∈ v.adicCompletionIntegers F
  by_cases hv : v ∈ hfinite.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d hv
    change n = d v * k at hk
    rw [hk, map_mul]
    have hdk : a v * algebraMap (𝓞 F) (v.adicCompletion F) (d v) ∈
        v.adicCompletionIntegers F := hda v
    have hkint : algebraMap (𝓞 F) (v.adicCompletion F) k ∈ v.adicCompletionIntegers F :=
      coe_mem_adicCompletionIntegers (K := F) v k
    have h := (v.adicCompletionIntegers F).mul_mem _ _ hdk hkint
    simpa only [mul_assoc, mul_comm (a v)] using h
  · have ha : a v ∈ v.adicCompletionIntegers F := by simpa using hv
    exact (v.adicCompletionIntegers F).mul_mem _ _
      (coe_mem_adicCompletionIntegers (K := F) v n) ha

/-- The additive number-field diagonal is dense in the finite adele ring. -/
theorem denseRange_scalarFiniteAdeles :
    DenseRange (algebraMap F (ScalarFiniteAdeles F)) := by
  let R := (algebraMap F (ScalarFiniteAdeles F)).range
  have hO : ∀ a : integralScalarAdeles F, a.val ∈ R.topologicalClosure := by
    intro a
    apply (denseRange_integralScalarEmbedding F).induction_on
      (p := fun a : integralScalarAdeles F => a.val ∈ R.topologicalClosure) a
      (R.isClosed_topologicalClosure.preimage continuous_subtype_val)
    intro d
    apply R.le_topologicalClosure
    refine ⟨(d : F), ?_⟩
    exact (IsScalarTower.algebraMap_apply (𝓞 F) F (ScalarFiniteAdeles F) d).symm
  intro a
  obtain ⟨d, hd, hda⟩ := exists_integralScalar_multiple F a
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd
  have hid : algebraMap F (ScalarFiniteAdeles F) ((d : F)⁻¹) *
      algebraMap (𝓞 F) (ScalarFiniteAdeles F) d = 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (ScalarFiniteAdeles F),
      ← map_mul, inv_mul_cancel₀ hdF, map_one]
  have h := R.topologicalClosure.mul_mem
    (R.le_topologicalClosure (Set.mem_range_self ((d : F)⁻¹)))
    (hO ⟨algebraMap (𝓞 F) (ScalarFiniteAdeles F) d * a, hda⟩)
  change a ∈ R.topologicalClosure
  simpa only [← mul_assoc, hid, one_mul] using h

end

/-! Additive approximation with all denominators confined to the selected
finite places. This supplies coefficients for the split unipotent subgroups. -/

open scoped Classical _root_.NumberField RestrictedProduct _root_.Topology
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] [NumberField F]

def integralOutside (T : Finset (HeightOneSpectrum (𝓞 F))) : Subring F :=
  ⨅ v : HeightOneSpectrum (𝓞 F), ⨅ (_ : v ∉ T), (v.valuation F).valuationSubring.toSubring

@[simp] theorem mem_integralOutside (T : Finset (HeightOneSpectrum (𝓞 F))) (a : F) :
    a ∈ integralOutside T ↔ ∀ v, v ∉ T → v.valuation F a ≤ 1 := by
  simp [integralOutside]

def scalarProjection (T : Finset (HeightOneSpectrum (𝓞 F))) :
    integralOutside T →+* ((v : T) → v.val.adicCompletion F) :=
  RingHom.pi fun v => (algebraMap F (v.val.adicCompletion F)).comp (integralOutside T).subtype

/-- Extend a finite scalar tuple by zero to a finite adele. -/
def extendScalarTuple (T : Finset (HeightOneSpectrum (𝓞 F)))
    (a : (v : T) → v.val.adicCompletion F) : ScalarFiniteAdeles F := by
  refine ⟨fun v : HeightOneSpectrum (𝓞 F) =>
    if hv : v ∈ T then a ⟨v, hv⟩ else (0 : v.adicCompletion F), ?_⟩
  have hc : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v ∉ T :=
    T.finite_toSet.compl_mem_cofinite
  apply hc.mono
  intro v hv
  simp only [dite_eq_right hv]
  exact (v.adicCompletionIntegers F).zero_mem

@[simp] theorem extendScalarTuple_apply (T : Finset (HeightOneSpectrum (𝓞 F)))
    (a : (v : T) → v.val.adicCompletion F) (v : HeightOneSpectrum (𝓞 F)) :
    extendScalarTuple T a v = if hv : v ∈ T then a ⟨v, hv⟩ else 0 := rfl

theorem denseRange_scalarProjection (T : Finset (HeightOneSpectrum (𝓞 F))) :
    DenseRange (scalarProjection T) := by
  intro a
  rw [mem_closure_iff]
  intro V hV ha
  obtain ⟨U, hU, hsub⟩ := isOpen_pi_iff'.mp hV a ha
  let W : Set (ScalarFiniteAdeles F) := {z |
    (∀ v : T, z v.val ∈ U v) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T → z v ∈ v.adicCompletionIntegers F}
  have hW : IsOpen W := by
    have hfirst : IsOpen {z : ScalarFiniteAdeles F | ∀ v : T, z v.val ∈ U v} := by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun v =>
        (hU v).1.preimage (RestrictedProduct.continuous_eval v.val)
    have hrest : IsOpen {z : ScalarFiniteAdeles F |
        ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T → z v ∈ v.adicCompletionIntegers F} :=
      RestrictedProduct.isOpen_forall_imp_mem
        (fun v : HeightOneSpectrum (𝓞 F) => Valued.isOpen_valuationSubring (v.adicCompletion F))
    exact hfirst.inter hrest
  let z := extendScalarTuple T a
  have hz : z ∈ W := by
    constructor
    · intro v
      have hv : v.val ∈ T := v.property
      simpa only [z, extendScalarTuple_apply, dite_eq_left hv] using (hU v).2
    · intro v hv
      change extendScalarTuple T a v ∈ v.adicCompletionIntegers F
      rw [extendScalarTuple_apply, dite_eq_right hv]
      exact (v.adicCompletionIntegers F).zero_mem
  obtain ⟨x, hx⟩ := (denseRange_scalarFiniteAdeles F).exists_mem_open hW ⟨z, hz⟩
  have hxi : x ∈ integralOutside T := by
    rw [mem_integralOutside]
    intro v hv
    have h := hx.2 v hv
    change Valued.v (x : v.adicCompletion F) ≤ 1 at h
    rwa [adicCompletion.valued_coe] at h
  let r : integralOutside T := ⟨x, hxi⟩
  refine ⟨scalarProjection T r, hsub ?_, Set.mem_range_self r⟩
  intro v _
  exact hx.1 v

end

end OAI.NumberTheory.Quaternion.Arithmetic.ScalarApproximation
