import OAI.NumberTheory.Adeles.FiniteNorm
import OAI.NumberTheory.Adeles.NormAlgebra

/-! # Completion Factors Finite Tensor -/

namespace OAI.NumberTheory.Adeles.CompletionFactorsFiniteTensor

noncomputable section

section

/-! Scalar extension and the finite completion factors. -/

open _root_.NumberField IsDedekindDomain HeightOneSpectrum
open scoped _root_.NumberField _root_.Topology TensorProduct OAI.NumberTheory.Adeles.LocalCompletions.CompletionFactors.FiniteLiesOver Valued

variable {F E : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def finiteTensorMapAt (w : FiniteNorm.CompletionFactors.FinitePlacesOver E v) :
    v.adicCompletion F ⊗[F] E →ₐ[v.adicCompletion F] w.val.adicCompletion E :=
  Algebra.TensorProduct.lift
    (Algebra.algHom (v.adicCompletion F) (v.adicCompletion F) (w.val.adicCompletion E))
    (Algebra.algHom F E (w.val.adicCompletion E)) (fun _ _ => mul_comm ..)

theorem finiteTensorMapAt_surjective (w : FiniteNorm.CompletionFactors.FinitePlacesOver E v) :
    Function.Surjective (finiteTensorMapAt v w) := by
  have hd : DenseRange (finiteTensorMapAt v w) := by
    apply (w.val.denseRange_algebraMap E).mono
    rintro _ ⟨x, rfl⟩
    refine ⟨1 ⊗ₜ[F] x, ?_⟩
    simp [finiteTensorMapAt, Algebra.algHom]
  change Function.Surjective (finiteTensorMapAt v w).toLinearMap
  rw [← Set.range_eq_univ, ← (finiteTensorMapAt v w).toLinearMap.coe_range,
    ← (finiteTensorMapAt v w).toLinearMap.range.closed_of_finiteDimensional.closure_eq]
  exact hd.closure_range

/-- A continuous local map compatible with the global field determines its prime. -/
theorem finitePlace_eq_of_localHom (w z : FiniteNorm.CompletionFactors.FinitePlacesOver E v)
    (f : w.val.adicCompletion E →ₐ[v.adicCompletion F] z.val.adicCompletion E)
    (hf : ∀ x : E, f (algebraMap E (w.val.adicCompletion E) x) =
      algebraMap E (z.val.adicCompletion E) x) : w = z := by
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  apply w.val.isMaximal.eq_of_le z.val.isPrime.ne_top
  intro a ha
  have hw : ‖FinitePlace.embedding w.val (a : E)‖ < 1 :=
    (FinitePlace.norm_lt_one_iff_mem E w.val a).mpr ha
  have ht := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hw
  have hc : Continuous f := f.toLinearMap.continuous_of_finiteDimensional
  have hx : f (FinitePlace.embedding w.val (a : E)) =
      FinitePlace.embedding z.val (a : E) := hf (a : E)
  have hz : Filter.Tendsto (fun n : ℕ =>
      (FinitePlace.embedding z.val (a : E)) ^ n) Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero, map_pow, hx] using (hc.tendsto 0).comp ht
  exact (FinitePlace.norm_lt_one_iff_mem E z.val a).mp
    (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp hz)

theorem finiteTensorMapAt_ker_pairwise :
    Pairwise (fun w z : FiniteNorm.CompletionFactors.FinitePlacesOver E v =>
      RingHom.ker (finiteTensorMapAt v w).toRingHom ≠
        RingHom.ker (finiteTensorMapAt v z).toRingHom) := by
  intro w z hwz hker
  let f := (finiteTensorMapAt v w).liftOfSurjective (finiteTensorMapAt_surjective v w)
    (finiteTensorMapAt v z) hker.le
  apply hwz
  apply finitePlace_eq_of_localHom v w z f
  intro x
  have h := AlgHom.liftOfSurjective_apply (finiteTensorMapAt v w)
    (finiteTensorMapAt_surjective v w) (finiteTensorMapAt v z) hker.le (1 ⊗ₜ[F] x)
  simpa [f, finiteTensorMapAt, Algebra.algHom] using h

abbrev FiniteBlock := (w : FiniteNorm.CompletionFactors.FinitePlacesOver E v) → w.val.adicCompletion E

def finiteTensorMap : v.adicCompletion F ⊗[F] E →ₐ[v.adicCompletion F] FiniteBlock (E := E) v :=
  AlgHom.pi fun w => finiteTensorMapAt v w

/-- Distinct completion factors are independent, by the Chinese remainder theorem. -/
theorem finiteTensorMap_surjective : Function.Surjective (finiteTensorMap (E := E) v) := by
  let I := fun w : FiniteNorm.CompletionFactors.FinitePlacesOver E v => RingHom.ker (finiteTensorMapAt v w).toRingHom
  let : ∀ w, (I w).IsMaximal := fun w =>
    RingHom.ker_isMaximal_of_surjective _ (finiteTensorMapAt_surjective v w)
  have hc : Pairwise (fun w z => IsCoprime (I w) (I z)) := by
    intro w z h
    exact Ideal.isCoprime_of_isMaximal (finiteTensorMapAt_ker_pairwise v h)
  let e := fun w : FiniteNorm.CompletionFactors.FinitePlacesOver E v =>
    Ideal.quotientKerAlgEquivOfSurjective (finiteTensorMapAt_surjective v w)
  intro a
  obtain ⟨b, hb⟩ := Ideal.pi_quotient_surjective hc (fun w => (e w).symm (a w))
  refine ⟨b, funext fun w => ?_⟩
  have h := congrArg (e w) (hb w)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h

end

section

/-! Global automorphisms and finite completion factors. -/

open _root_.NumberField IsDedekindDomain HeightOneSpectrum
open scoped _root_.NumberField _root_.Topology TensorProduct OAI.NumberTheory.Adeles.LocalCompletions.CompletionFactors.FiniteLiesOver Valued

variable {F E : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def finitePlaceConjugate (σ : E ≃ₐ[F] E) (w : FiniteNorm.CompletionFactors.FinitePlacesOver E v) :
    FiniteNorm.CompletionFactors.FinitePlacesOver E v := by
  let e := RingOfIntegers.mapAlgEquiv σ
  let z := HeightOneSpectrum.comap e.toRingHom e.surjective w.val
  refine ⟨z, ?_⟩
  rw [Ideal.liesOver_iff]
  change v.asIdeal = Ideal.comap (algebraMap (𝓞 F) (𝓞 E))
    (Ideal.comap e.toRingHom w.val.asIdeal)
  rw [Ideal.comap_comap]
  have he : e.toRingHom.comp (algebraMap (𝓞 F) (𝓞 E)) =
      algebraMap (𝓞 F) (𝓞 E) := RingHom.ext fun x => e.commutes x
  rw [he]
  exact Ideal.over_def w.val.asIdeal v.asIdeal

omit [NumberField F] in
theorem finitePlaceConjugate_eq_of_unique [Subsingleton (FiniteNorm.CompletionFactors.FinitePlacesOver E v)]
    (σ : E ≃ₐ[F] E) (w : FiniteNorm.CompletionFactors.FinitePlacesOver E v) :
    w.val.asIdeal.comap (RingOfIntegers.mapRingHom σ.toRingHom) = w.val.asIdeal := by
  exact congrArg (fun z : FiniteNorm.CompletionFactors.FinitePlacesOver E v => z.val.asIdeal)
    (Subsingleton.elim (finitePlaceConjugate v σ w) w)

theorem intValuation_equiv (w : HeightOneSpectrum (𝓞 E)) (σ : E ≃+* E)
    (hw : w.asIdeal.comap (RingOfIntegers.mapRingHom σ.toRingHom) = w.asIdeal)
    (x : 𝓞 E) : w.intValuation (RingOfIntegers.mapRingHom σ.toRingHom x) =
      w.intValuation x := by
  let e := RingOfIntegers.mapRingEquiv σ
  let eI : Ideal (𝓞 E) ≃* Ideal (𝓞 E) :=
    { e.idealComapOrderIso.symm.toEquiv with
      map_mul' := fun I J => Ideal.map_mul e.toRingHom I J }
  have hwe : eI w.asIdeal = w.asIdeal := by
    change w.asIdeal.map e.toRingHom = w.asIdeal
    nth_rw 1 [← hw]
    exact Ideal.map_comap_eq_self_of_equiv e w.asIdeal
  by_cases hx : x = 0
  · simp [hx]
  change w.intValuation (e x) = w.intValuation x
  rw [w.intValuation_eq_exp_neg_multiplicity
      (fun h => hx (e.injective (h.trans (map_zero e).symm))),
    w.intValuation_eq_exp_neg_multiplicity hx]
  have hm := multiplicity_map_eq eI (a := w.asIdeal) (b := Ideal.span {x})
  rw [hwe] at hm
  change multiplicity w.asIdeal ((Ideal.span {x}).map e.toRingHom) = _ at hm
  rw [Ideal.map_span, Set.image_singleton] at hm
  exact congrArg (fun n : ℕ => WithZero.exp (-(n : ℤ))) hm

theorem valuation_equiv (w : HeightOneSpectrum (𝓞 E)) (σ : E ≃+* E)
    (hw : w.asIdeal.comap (RingOfIntegers.mapRingHom σ.toRingHom) = w.asIdeal)
    (x : E) : w.valuation E (σ x) = w.valuation E x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  simp only [map_div₀]
  have ha : w.valuation E (σ (algebraMap (𝓞 E) E a)) = w.valuation E
      (algebraMap (𝓞 E) E a) := by
    change w.valuation E (algebraMap (𝓞 E) E (RingOfIntegers.mapRingHom σ.toRingHom a)) = _
    simpa only [valuation_of_algebraMap] using intValuation_equiv w σ hw a
  have hb' : w.valuation E (σ (algebraMap (𝓞 E) E b)) = w.valuation E
      (algebraMap (𝓞 E) E b) := by
    change w.valuation E (algebraMap (𝓞 E) E (RingOfIntegers.mapRingHom σ.toRingHom b)) = _
    simpa only [valuation_of_algebraMap] using intValuation_equiv w σ hw b
  rw [ha, hb']

def finiteValuedAutomorphism (w : HeightOneSpectrum (𝓞 E)) (σ : E ≃+* E) :
    WithVal (w.valuation E) ≃+* WithVal (w.valuation E) :=
  ((WithVal.equiv (w.valuation E)).trans σ).trans (WithVal.equiv (w.valuation E)).symm

theorem uniformContinuous_finiteValuedAutomorphism (w : HeightOneSpectrum (𝓞 E))
    (σ : E ≃+* E)
    (hw : w.asIdeal.comap (RingOfIntegers.mapRingHom σ.toRingHom) = w.asIdeal) :
    UniformContinuous (finiteValuedAutomorphism w σ).toRingHom := by
  apply uniformContinuous_of_continuousAt_zero (finiteValuedAutomorphism w σ).toAddMonoidHom
  rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero (WithVal (w.valuation E)) _).tendsto_iff
      (Valued.hasBasis_nhds_zero (WithVal (w.valuation E)) _)]
  intro γ _
  refine ⟨γ, trivial, ?_⟩
  intro x hx
  change Valued.v.restrict x < γ.val at hx
  change Valued.v.restrict (finiteValuedAutomorphism w σ x) < γ.val
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  change w.valuation E (σ (WithVal.equiv _ x)) < _
  rw [valuation_equiv w σ hw]
  exact hx

def finiteCompletionAutomorphism (w : HeightOneSpectrum (𝓞 E)) (σ : E ≃+* E)
    (hw : w.asIdeal.comap (RingOfIntegers.mapRingHom σ.toRingHom) = w.asIdeal) :
    w.adicCompletion E →+* w.adicCompletion E :=
  ((adicCompletion.equiv E w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom (finiteValuedAutomorphism w σ).toRingHom
      (uniformContinuous_finiteValuedAutomorphism w σ hw).continuous)).comp
        (adicCompletion.equiv E w).toRingHom

theorem continuous_finiteCompletionAutomorphism (w : HeightOneSpectrum (𝓞 E))
    (σ : E ≃+* E)
    (hw : w.asIdeal.comap (RingOfIntegers.mapRingHom σ.toRingHom) = w.asIdeal) :
    Continuous (finiteCompletionAutomorphism w σ hw) :=
  (adicCompletion.continuous_ofCompletion E w).comp
    (UniformSpace.Completion.continuous_map.comp
      (adicCompletion.continuous_toCompletion E w))

@[simp] theorem finiteCompletionAutomorphism_coe (w : HeightOneSpectrum (𝓞 E))
    (σ : E ≃+* E)
    (hw : w.asIdeal.comap (RingOfIntegers.mapRingHom σ.toRingHom) = w.asIdeal) (x : E) :
    finiteCompletionAutomorphism w σ hw (algebraMap E (w.adicCompletion E) x) =
      algebraMap E (w.adicCompletion E) (σ x) := by
  apply adicCompletion.ext
  change UniformSpace.Completion.mapRingHom (finiteValuedAutomorphism w σ).toRingHom _
    ((WithVal.equiv (w.valuation E)).symm x : UniformSpace.Completion _) = _
  exact UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_finiteValuedAutomorphism w σ hw).continuous
    ((WithVal.equiv (w.valuation E)).symm x)

theorem finiteCompletionAutomorphism_base (σ : E ≃ₐ[F] E) (w : FiniteNorm.CompletionFactors.FinitePlacesOver E v)
    (hw : w.val.asIdeal.comap (RingOfIntegers.mapRingHom σ.toRingHom) = w.val.asIdeal)
    (a : v.adicCompletion F) :
    finiteCompletionAutomorphism w.val σ.toRingEquiv hw (LocalCompletions.CompletionFactors.finiteCompletionMap v w.val a) =
      LocalCompletions.CompletionFactors.finiteCompletionMap v w.val a := by
  apply (v.denseRange_algebraMap F).induction_on (p := fun a =>
    finiteCompletionAutomorphism w.val σ.toRingEquiv hw (LocalCompletions.CompletionFactors.finiteCompletionMap v w.val a) =
      LocalCompletions.CompletionFactors.finiteCompletionMap v w.val a) a
  · exact isClosed_eq
      ((continuous_finiteCompletionAutomorphism w.val σ.toRingEquiv hw).comp
        (LocalCompletions.CompletionFactors.continuous_finiteCompletionMap v w.val)) (LocalCompletions.CompletionFactors.continuous_finiteCompletionMap v w.val)
  · intro x
    change finiteCompletionAutomorphism w.val σ.toRingEquiv hw
      (LocalCompletions.CompletionFactors.finiteCompletionMap v w.val (x : v.adicCompletion F)) =
        LocalCompletions.CompletionFactors.finiteCompletionMap v w.val (x : v.adicCompletion F)
    rw [LocalCompletions.CompletionFactors.finiteCompletionMap_coe]
    change finiteCompletionAutomorphism w.val σ.toRingEquiv hw
      (algebraMap E (w.val.adicCompletion E) (algebraMap F E x)) = _
    rw [finiteCompletionAutomorphism_coe]
    exact congrArg (algebraMap E (w.val.adicCompletion E)) (σ.commutes x)

theorem globalAutomorphism_eq_one_of_unique_local_degree_one
    [Subsingleton (FiniteNorm.CompletionFactors.FinitePlacesOver E v)] (w : FiniteNorm.CompletionFactors.FinitePlacesOver E v)
    (hd : Module.finrank (v.adicCompletion F) (w.val.adicCompletion E) = 1)
    (σ : E ≃ₐ[F] E) : σ = 1 := by
  have hs := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd).surjective
  have hw := finitePlaceConjugate_eq_of_unique v σ w
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E (w.val.adicCompletion E)).injective
  change algebraMap E (w.val.adicCompletion E) (σ.toRingEquiv x) =
    algebraMap E (w.val.adicCompletion E) x
  rw [← finiteCompletionAutomorphism_coe w.val σ.toRingEquiv hw]
  obtain ⟨a, ha⟩ := hs (algebraMap E (w.val.adicCompletion E) x)
  change LocalCompletions.CompletionFactors.finiteCompletionMap v w.val a = _ at ha
  rw [← ha]
  exact finiteCompletionAutomorphism_base v σ w hw a

end

/-! The finite completion decomposition for a quadratic extension. -/

open _root_.NumberField IsDedekindDomain HeightOneSpectrum
open scoped _root_.NumberField _root_.Topology TensorProduct OAI.NumberTheory.Adeles.LocalCompletions.CompletionFactors.FiniteLiesOver Valued

variable {F E : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

instance finitePlacesOver_nonempty : Nonempty (FiniteNorm.CompletionFactors.FinitePlacesOver E v) := by
  obtain ⟨q⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
  let : q.val.IsPrime := q.property.1
  let : q.val.LiesOver v.asIdeal := q.property.2
  exact ⟨⟨⟨q.val, q.property.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.val⟩,
    q.property.2⟩⟩

instance finiteBlock_finiteDimensional :
    FiniteDimensional (v.adicCompletion F) (FiniteBlock (E := E) v) := inferInstance

theorem finiteBlock_finrank_quadratic (hQuadratic : Module.finrank F E = 2) :
    Module.finrank (v.adicCompletion F) (FiniteBlock (E := E) v) = 2 := by
  classical
  let : Algebra.IsQuadraticExtension F E := ⟨hQuadratic⟩
  have hle : Module.finrank (v.adicCompletion F) (FiniteBlock (E := E) v) ≤ 2 := by
    have h := LinearMap.finrank_le_finrank_of_surjective
      (f := (finiteTensorMap (E := E) v).toLinearMap) (finiteTensorMap_surjective v)
    simpa only [Module.finrank_baseChange, hQuadratic] using h
  have hpos : 0 < Module.finrank (v.adicCompletion F) (FiniteBlock (E := E) v) :=
    Module.finrank_pos
  by_contra hne
  have hone : Module.finrank (v.adicCompletion F) (FiniteBlock (E := E) v) = 1 := by omega
  have hsum : (∑ w : FiniteNorm.CompletionFactors.FinitePlacesOver E v,
      Module.finrank (v.adicCompletion F) (w.val.adicCompletion E)) = 1 := by
    simpa only [FiniteBlock, Module.finrank_pi_fintype] using hone
  have hcard : Fintype.card (FiniteNorm.CompletionFactors.FinitePlacesOver E v) ≤ 1 := by
    calc
      _ = ∑ _w : FiniteNorm.CompletionFactors.FinitePlacesOver E v, 1 := by simp
      _ ≤ ∑ w : FiniteNorm.CompletionFactors.FinitePlacesOver E v,
          Module.finrank (v.adicCompletion F) (w.val.adicCompletion E) :=
        Finset.sum_le_sum fun w _ => Module.finrank_pos
      _ = 1 := hsum
  let : Subsingleton (FiniteNorm.CompletionFactors.FinitePlacesOver E v) := Fintype.card_le_one_iff_subsingleton.mp hcard
  let w := Classical.choice (finitePlacesOver_nonempty (E := E) v)
  have hd : Module.finrank (v.adicCompletion F) (w.val.adicCompletion E) = 1 := by
    rw [Finset.sum_eq_single w (fun z _ hzw => (hzw (Subsingleton.elim z w)).elim)
      (fun h => (h (Finset.mem_univ w)).elim)] at hsum
    exact hsum
  let : Subsingleton (E ≃ₐ[F] E) := ⟨fun σ τ =>
    (globalAutomorphism_eq_one_of_unique_local_degree_one v w hd σ).trans
      (globalAutomorphism_eq_one_of_unique_local_degree_one v w hd τ).symm⟩
  have hc := IsGalois.card_aut_eq_finrank F E
  have hsmall : Nat.card (E ≃ₐ[F] E) ≤ 1 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  rw [hc, hQuadratic] at hsmall
  omega

def finiteTensorEquivQuadratic (hQuadratic : Module.finrank F E = 2) :
    v.adicCompletion F ⊗[F] E ≃ₐ[v.adicCompletion F] FiniteBlock (E := E) v :=
  AlgEquiv.ofBijective (finiteTensorMap v) (by
    have hd : Module.finrank (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) =
        Module.finrank (v.adicCompletion F) (FiniteBlock (E := E) v) := by
      rw [Module.finrank_baseChange, finiteBlock_finrank_quadratic v hQuadratic, hQuadratic]
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (finiteTensorMap (E := E) v).toLinearMap) hd).mpr
      (finiteTensorMap_surjective v), finiteTensorMap_surjective v⟩)

end

end OAI.NumberTheory.Adeles.CompletionFactorsFiniteTensor
