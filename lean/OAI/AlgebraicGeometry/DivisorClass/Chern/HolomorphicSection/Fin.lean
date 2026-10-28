import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TensorSection
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Nonzero

/-! # Fin -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Fin

noncomputable section

section

/-! Actual positive powers of original holomorphic sections, retaining nonzero original point values. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

def holomorphicSectionCast {u v : Holomorphic.Connecting.holomorphicUnitCohomology E M} (h : u = v)
    (s : Data.HolomorphicLineSection u ⊤) : Data.HolomorphicLineSection v ⊤ := h ▸ s

theorem holomorphicSectionCast_nonzero {u v : Holomorphic.Connecting.holomorphicUnitCohomology E M} (h : u = v)
    (s : Data.HolomorphicLineSection u ⊤) (x : M) (hs : Nonzero.holomorphicSectionNonzeroAt u s x) :
    Nonzero.holomorphicSectionNonzeroAt v (holomorphicSectionCast h s) x := by
  cases h
  exact hs

def holomorphicSectionPositivePower (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (s : Data.HolomorphicLineSection u ⊤) :
    (n : ℕ) → Data.HolomorphicLineSection ((n + 1) • u) ⊤
  | 0 => holomorphicSectionCast (by simp) s
  | n + 1 => holomorphicSectionCast (by simp only [add_nsmul, one_nsmul])
      (Holomorphic.TensorSection.holomorphicTensorSection ((n + 1) • u) u (holomorphicSectionPositivePower u s n) s)

theorem holomorphicSectionPositivePower_nonzero (u : Holomorphic.Connecting.holomorphicUnitCohomology E M)
    (s : Data.HolomorphicLineSection u ⊤) (x : M) (hs : Nonzero.holomorphicSectionNonzeroAt u s x) (n : ℕ) :
    Nonzero.holomorphicSectionNonzeroAt ((n + 1) • u) (HolomorphicSection.Fin.holomorphicSectionPositivePower u s n) x := by
  induction n with
  | zero => exact holomorphicSectionCast_nonzero _ s x hs
  | succ n ih =>
    apply holomorphicSectionCast_nonzero
    exact Holomorphic.TensorSection.holomorphicTensorSection_nonzero ((n + 1) • u) u (HolomorphicSection.Fin.holomorphicSectionPositivePower u s n) s x ih hs

theorem exists_holomorphicSection_power_nonzero (u : Holomorphic.Connecting.holomorphicUnitCohomology E M)
    (s : Data.HolomorphicLineSection u ⊤) (x : M) (hs : Nonzero.holomorphicSectionNonzeroAt u s x)
    (n : ℕ) (hn : 0 < n) : ∃ t : Data.HolomorphicLineSection (n • u) ⊤, Nonzero.holomorphicSectionNonzeroAt (n • u) t x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact ⟨HolomorphicSection.Fin.holomorphicSectionPositivePower u s k, holomorphicSectionPositivePower_nonzero u s x hs k⟩

end

section

/-! Compactness and actual section powers turn pointwise positive multiples into one globally generated original multiple. -/

open Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

def holomorphicLineGloballyGenerated (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) : Prop :=
  ∀ x : M, ∃ s : Data.HolomorphicLineSection u ⊤, Nonzero.holomorphicSectionNonzeroAt u s x

theorem exists_holomorphic_globally_generated_multiple [CompactSpace M]
    (v : Holomorphic.Connecting.holomorphicUnitCohomology E M)
    (hv : ∀ x : M, ∃ n : ℕ, 0 < n ∧ ∃ s : Data.HolomorphicLineSection (n • v) ⊤,
      Nonzero.holomorphicSectionNonzeroAt (n • v) s x) :
    ∃ N : ℕ, 0 < N ∧ holomorphicLineGloballyGenerated (N • v) := by
  classical
  choose n hn s hs using hv
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun y : M => {x | Nonzero.holomorphicSectionNonzeroAt (n y • v) (s y) x})
    (fun y => Nonzero.holomorphicSectionNonzeroAt_isOpen (n y • v) (s y))
    (fun x _ => mem_iUnion.mpr ⟨x, hs x⟩)
  let N := ∏ y ∈ F, n y
  have hN : 0 < N := Finset.prod_pos (fun y _ => hn y)
  refine ⟨N, hN, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ F, Nonzero.holomorphicSectionNonzeroAt (n y • v) (s y) x := by
    simpa only [mem_iUnion, exists_prop, mem_ofPred_eq] using! hF (mem_univ x)
  have hd : n y ∣ N := Finset.dvd_prod_of_mem (fun z => n z) hy
  have hm : 0 < N / n y := Nat.div_pos (Nat.le_of_dvd hN hd) (hn y)
  obtain ⟨t, ht⟩ := exists_holomorphicSection_power_nonzero (n y • v) (s y) x hxy (N / n y) hm
  have heq : (N / n y) • (n y • v) = N • v := by rw [smul_smul, Nat.div_mul_cancel hd]
  exact ⟨holomorphicSectionCast heq t, holomorphicSectionCast_nonzero heq t x ht⟩

end

/-! A genuinely globally generated original line bundle has a finite original holomorphic section family with no common zero. -/

open Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M]

theorem exists_finite_holomorphic_generators (u : Holomorphic.Connecting.holomorphicUnitCohomology E M)
    (hu : holomorphicLineGloballyGenerated u) :
    ∃ F : Finset (Data.HolomorphicLineSection u ⊤), ∀ x : M, ∃ s ∈ F, Nonzero.holomorphicSectionNonzeroAt u s x := by
  classical
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun s : Data.HolomorphicLineSection u ⊤ => {x | Nonzero.holomorphicSectionNonzeroAt u s x})
    (fun s => Nonzero.holomorphicSectionNonzeroAt_isOpen u s)
    (by
      intro x _
      obtain ⟨s, hs⟩ := hu x
      exact mem_iUnion.mpr ⟨s, hs⟩)
  refine ⟨F, fun x => ?_⟩
  simpa only [mem_iUnion, exists_prop, mem_ofPred_eq] using! hF (mem_univ x)

theorem exists_fin_holomorphic_generators (u : Holomorphic.Connecting.holomorphicUnitCohomology E M)
    (hu : holomorphicLineGloballyGenerated u) :
    ∃ n : ℕ, ∃ s : Fin (n + 1) → Data.HolomorphicLineSection u ⊤,
      ∀ x : M, ∃ j, Nonzero.holomorphicSectionNonzeroAt u (s j) x := by
  classical
  obtain ⟨F, hF⟩ := exists_finite_holomorphic_generators u hu
  let : Nonempty (Option F) := ⟨none⟩
  let e : Option F ≃ Fin (F.card + 1) := Fintype.equivFinOfCardEq (by
    simp only [Fintype.card_option, Fintype.card_coe])
  let q : Option F → Data.HolomorphicLineSection u ⊤ := fun o => o.elim 0 Subtype.val
  refine ⟨F.card, fun j => q (e.symm j), fun x => ?_⟩
  obtain ⟨s, hs, hx⟩ := hF x
  refine ⟨e (some ⟨s, hs⟩), ?_⟩
  simpa only [Equiv.symm_apply_apply, q, Option.elim_some] using! hx

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Fin
