import OAI.RepresentationTheory.Weil.AdelicSplitting.Characters

/-! # Unramified Character -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.UnramifiedCharacter.Construction

noncomputable section

/-! Continuity forces a unitary adelic additive character to be trivial
on the integer rings at all but finitely many finite places. -/

open Filter
open scoped Classical _root_.NumberField _root_.Topology

theorem eventually_cofinite_sum_right {I J : Type*} (p : J → Prop)
    (hp : ∀ᶠ j in cofinite, p j) :
    ∀ᶠ v : I ⊕ J in cofinite, match v with | .inl _ => True | .inr j => p j := by
  rw [eventually_cofinite]
  have h := (eventually_cofinite.mp hp).image (Sum.inr : J → I ⊕ J)
  convert h using 1
  ext v
  cases v <;> simp

theorem circle_character_product_tail
    {I : Type*} {A : I → Type*} [∀ i, AddCommGroup (A i)]
    [∀ i, TopologicalSpace (A i)]
    (χ : AddChar (∀ i, A i) Circle) (hχ : Continuous χ) :
    ∃ s : Finset I, ∀ i ∉ s, ∀ a : A i, χ (Pi.single i a) = 1 := by
  have hz : χ 0 ∈ Circle.centeredArc (Real.pi / 2) := by
    rw [χ.map_zero_eq_one]
    exact ⟨0, by simpa using (half_pos Real.pi_pos), Circle.exp_zero⟩
  obtain ⟨s, U, hU, hs⟩ := isOpen_pi_iff.mp
    ((Circle.isOpen_centeredArc _).preimage hχ) 0 hz
  have hsingle (i : I) (hi : i ∉ s) (a : A i) :
      χ (Pi.single i a) ∈ Circle.centeredArc (Real.pi / 2) := by
    apply hs
    intro j hj
    rw [Pi.single_eq_of_ne (show j ≠ i from fun h => hi (h ▸ hj))]
    exact (hU j hj).2
  refine ⟨s, ?_⟩
  intro i hi a
  apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
  intro n _
  rw [← χ.map_nsmul_eq_pow]
  have he : n • Pi.single i a = Pi.single i (n • a) := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]
  rw [he]
  exact hsingle i hi _

variable (F : Type) [Field F] [NumberField F]

def integralFiniteAdeles :
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+ ArchimedeanAdeles.Construction.Adeles F where
  toFun x := (0, ⟨fun v => (x v).val, Filter.Eventually.of_forall (fun v => (x v).property)⟩)
  map_zero' := by
    apply Prod.ext
    · rfl
    · apply RestrictedProduct.ext; intro v; rfl
  map_add' x y := by
    apply Prod.ext
    · exact (add_zero 0).symm
    · apply RestrictedProduct.ext; intro v; rfl

theorem integralFiniteAdeles_continuous : Continuous (integralFiniteAdeles F) := by
  let f : (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →
      RestrictedProduct (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ⊤ :=
    fun x => ⟨fun v => (x v).val, fun v => (x v).property⟩
  have hf : Continuous f := by
    apply RestrictedProduct.continuous_rng_of_top.mpr
    exact continuous_pi (fun v => continuous_subtype_val.comp (continuous_apply v))
  exact continuous_const.prodMk ((RestrictedProduct.continuous_inclusion le_top).comp hf)

theorem integralFiniteAdeles_single
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (a : v.adicCompletionIntegers F) :
    integralFiniteAdeles F (Pi.single v a) = ArchimedeanAdeles.Construction.localAdd F (Sum.inr v) a.val := by
  apply Prod.ext
  · rfl
  · apply RestrictedProduct.ext
    intro w
    change ((Pi.single v a : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      p.adicCompletionIntegers F) w).val =
      RestrictedProduct.single
        (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => p.adicCompletionIntegers F) v a.val w
    by_cases h : w = v
    · subst w; simp
    · simp [Pi.single_eq_of_ne h, RestrictedProduct.single_eq_of_ne _ _ h]

theorem localAdditiveCharacter_unramified_finite
    (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hu : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ) :
    ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ x ∈ v.adicCompletionIntegers F, Characters.Construction.localAdditiveCharacter F ψ (Sum.inr v) x = 1 := by
  let χ : AddChar (ArchimedeanAdeles.Construction.Adeles F) Circle :=
    { toFun := fun x => ⟨ψ x, mem_sphere_zero_iff_norm.mpr (hu x)⟩
      map_zero_eq_one' := Subtype.ext ψ.map_zero_eq_one
      map_add_eq_mul' := fun x y => Subtype.ext (ψ.map_add_eq_mul x y) }
  have hχ : Continuous χ := hc.subtype_mk _
  obtain ⟨s, hs⟩ := circle_character_product_tail
    (χ.compAddMonoidHom (integralFiniteAdeles F)) (hχ.comp (integralFiniteAdeles_continuous F))
  have ht : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in cofinite, v ∉ s :=
    s.finite_toSet.compl_mem_cofinite
  filter_upwards [ht] with v hv
  intro x hx
  have h := hs v hv ⟨x, hx⟩
  change χ (integralFiniteAdeles F (Pi.single v ⟨x, hx⟩)) = 1 at h
  rw [integralFiniteAdeles_single] at h
  exact congrArg (fun z : Circle => (z : ℂ)) h

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.UnramifiedCharacter.Construction
