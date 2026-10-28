import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBanked

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryModelBudgets
open SqrtLog SqrtLog.LeafParametersProgram Circuit

/-- The serializer changes only two previously empty numeric ports. -/
theorem serialized_model_values_le (x : Input) (padding : Fin 8 → ℕ) (S : ℕ)
    (h : ∀ j, (result Serialization.code (Execute.guardedModel x padding)).val j ≤ S) :
    ∀ j, (Execute.guardedModel x padding).val j ≤ S := by
  intro j
  by_cases h44 : j = 44
  · subst j
    simp [Execute.guardedModel, Fin.coe_ofNat_eq_mod]
  by_cases h45 : j = 45
  · subst j
    simp [Execute.guardedModel, Fin.coe_ofNat_eq_mod]
  exact (Serialization.frame _ j h44 h45) ▸ h j

/-- Physical serialized length caps also bound every pre-serialization word;
no numeric value is used as a replacement for a padded word length. -/
theorem serialized_model_lengths_le (x : Input) (padding : Fin 8 → ℕ) (S : ℕ)
    (h : ∀ j, (result Serialization.code (Execute.guardedModel x padding)).len j ≤ S) :
    ∀ j, (Execute.guardedModel x padding).len j ≤ S := by
  intro j
  by_cases h44 : j = 44
  · subst j
    simp [Execute.guardedModel, Fin.coe_ofNat_eq_mod]
  by_cases h45 : j = 45
  · subst j
    simp [Execute.guardedModel, Fin.coe_ofNat_eq_mod]
  have hj := h j
  simpa [Serialization.code, result, next, output, lengthBound, h44, h45] using hj

/-- Every literal packing scalar is read from the actual guarded bank.
This statement is independent of a supplied packing problem or layout. -/
theorem produced_layout_scalars_le (x : Input) (padding : Fin 8 → ℕ) (S : ℕ)
    (hv : ∀ j, (Execute.guardedModel x padding).val j ≤ S) :
    x.ambient ≤ S ∧ x.factors ≤ S ∧ x.incidences ≤ S ∧
      (produce x).r ≤ S ∧ (produce x).Q ≤ S ∧ (produce x).epsilonDen ≤ S ∧
      (produce x).r ^ (produce x).Q ≤ S ∧
      (produce x).r ^ (2 * (produce x).Q) ≤ S ∧ (produce x).R ≤ S := by
  have hn := hv 0
  have hf := hv 5
  have hi := hv 7
  have he0 : (Execute.guardedModel x padding).val 0 = x.ambient :=
    Execute.guardedModel_input x padding 0
  have he5 : (Execute.guardedModel x padding).val 5 = x.factors :=
    Execute.guardedModel_input x padding 5
  have he7 : (Execute.guardedModel x padding).val 7 = x.incidences :=
    Execute.guardedModel_input x padding 7
  rw [he0] at hn
  rw [he5] at hf
  rw [he7] at hi
  have hr := hv 18
  rw [Execute.guardedModel_radius] at hr
  obtain ⟨_, _, _, _, hQ, hs, hR, hN⟩ := Layout.model_core_values x padding
  have hQ' := hv 21
  have hs' := hv 25
  have hR' := hv 29
  have hN' := hv 31
  have heQ : (Execute.guardedModel x padding).val 21 = (produce x).Q :=
    (Execute.guardedModel_public x padding 4).trans hQ
  have heS : (Execute.guardedModel x padding).val 25 = (produce x).epsilonDen :=
    (Execute.guardedModel_public x padding 5).trans hs
  have heR : (Execute.guardedModel x padding).val 29 = (produce x).R :=
    (Execute.guardedModel_public x padding 6).trans hR
  have heN : (Execute.guardedModel x padding).val 31 = (produce x).N :=
    (Execute.guardedModel_public x padding 7).trans hN
  rw [heQ] at hQ'
  rw [heS] at hs'
  rw [heR] at hR'
  rw [heN] at hN'
  refine ⟨hn, hf, hi, hr, hQ', hs', ?_, hN', hR'⟩
  apply le_trans _ hN'
  change (produce x).r ^ (produce x).Q ≤ (produce x).r ^ (2 * (produce x).Q)
  exact Nat.pow_le_pow_right (by have := produce_r_ge_two x; omega) (by omega)

/-- Nonempty-query precision, extension dimension and jet order are the
actual public bank outputs. Their values, rather than word lengths, control
all dense ring-array dimensions. -/
theorem produced_ring_scalars_le (x : Input) (padding : Fin 8 → ℕ) (S : ℕ)
    (hm : x.clauses ≠ 0) (hQ : (produce x).Q ≠ 0)
    (hv : ∀ j, (Execute.guardedModel x padding).val j ≤ S) :
    (produce x).t ≤ S ∧ (produce x).d ≤ S ∧ (produce x).J ≤ S := by
  have ht := hv 33
  have hd := hv 34
  have hJ := hv 42
  rw [Execute.guardedModel_precision x padding hm] at ht
  rw [Execute.guardedModel_degree x padding hQ] at hd
  have hj : (Execute.guardedModel x padding).val 42 = (produce x).J :=
    (Execute.guardedModel_public x padding 11).trans (Layout.model_jet x padding hm hQ)
  rw [hj] at hJ
  exact ⟨ht, hd, hJ⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryModelBudgets
