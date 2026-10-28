import OAI.RepresentationTheory.Theta.Adelic.IntegralQuadraticIdeles

/-! # Hecke Unramified -/

namespace OAI.RepresentationTheory.Theta.Adelic.HeckeUnramified

noncomputable section

/-! Every continuous quadratic Hecke character is trivial on the full
integral quadratic unit group at almost every finite place. -/

open Filter
open scoped Classical _root_.NumberField _root_.Topology

open OAI.RepresentationTheory.Theta.Adelic.IntegralQuadraticIdeles

theorem circle_multiplicative_product_tail
    {I : Type*} {A : I → Type*} [∀ i, CommGroup (A i)]
    [∀ i, TopologicalSpace (A i)]
    (χ : (∀ i, A i) →* Circle) (hχ : Continuous χ) :
    ∃ s : Finset I, ∀ i ∉ s, ∀ a : A i, χ (Pi.mulSingle i a) = 1 := by
  have hz : χ 1 ∈ Circle.centeredArc (Real.pi / 2) := by
    rw [χ.map_one]
    exact ⟨0, by simpa using (half_pos Real.pi_pos), Circle.exp_zero⟩
  obtain ⟨s, U, hU, hs⟩ := isOpen_pi_iff.mp
    ((Circle.isOpen_centeredArc _).preimage hχ) 1 hz
  have hsingle (i : I) (hi : i ∉ s) (a : A i) :
      χ (Pi.mulSingle i a) ∈ Circle.centeredArc (Real.pi / 2) := by
    apply hs
    intro j hj
    rw [Pi.mulSingle_eq_of_ne (show j ≠ i from fun h => hi (h ▸ hj))]
    exact (hU j hj).2
  refine ⟨s, ?_⟩
  intro i hi a
  apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
  intro n _
  rw [← χ.map_pow]
  have he : Pi.mulSingle i a ^ n = Pi.mulSingle i (a ^ n) := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Pi.mulSingle_eq_of_ne h]
  rw [he]
  exact hsingle i hi _

variable (F : Type) [Field F] [NumberField F] (d : F)

theorem localCharacter_unramified_finite (χ : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ →ₜ* Circle) :
    ∀ᶠ v : IntegralQuadraticIdeles.FinitePlace F in cofinite, ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v))ˣ,
      a.val ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v) → a.inv ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v) →
      Weil.AdelicSplitting.Characters.Construction.localCharacter F d χ (.inr v) a = 1 := by
  obtain ⟨s, hs⟩ := circle_multiplicative_product_tail
    (χ.toMonoidHom.comp (IntegralQuadraticIdeles.productIdele F d))
      (χ.continuous.comp (IntegralQuadraticIdeles.productIdele_continuous F d))
  have ht : ∀ᶠ v : IntegralQuadraticIdeles.FinitePlace F in cofinite, v ∉ s := s.finite_toSet.compl_mem_cofinite
  have hd : ∀ᶠ v : IntegralQuadraticIdeles.FinitePlace F in cofinite,
      Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) :=
    (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d).property
  filter_upwards [ht, hd] with v hv hd
  intro a ha hi
  let b : IntegralQuadraticIdeles.goodIntegralUnits F d v := ⟨a, by
    rw [IntegralQuadraticIdeles.goodIntegralUnits, ite_eq_left hd]
    exact ⟨ha, hi⟩⟩
  have h := hs v hv b
  change χ (IntegralQuadraticIdeles.productIdele F d (Pi.mulSingle v b)) = 1 at h
  rw [IntegralQuadraticIdeles.productIdele_single] at h
  exact h

theorem localCharacter_unramified (χ : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ →ₜ* Circle) :
    ∀ᶠ v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F in cofinite, ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ,
      a.val ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v → a.inv ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v →
      Weil.AdelicSplitting.Characters.Construction.localCharacter F d χ v a = 1 := by
  have h := Weil.AdelicSplitting.UnramifiedCharacter.Construction.eventually_cofinite_sum_right (I := NumberField.InfinitePlace F) _
    (localCharacter_unramified_finite F d χ)
  have hi : ∀ᶠ v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F in cofinite, v ∉ Set.range Sum.inl :=
    (Set.finite_range (Sum.inl : NumberField.InfinitePlace F → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)).compl_mem_cofinite
  filter_upwards [h, hi] with v hv hi
  cases v with
  | inl v => exact False.elim (hi ⟨v, rfl⟩)
  | inr v => exact hv

end

end OAI.RepresentationTheory.Theta.Adelic.HeckeUnramified
