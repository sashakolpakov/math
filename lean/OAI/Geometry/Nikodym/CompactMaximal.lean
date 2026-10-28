import Mathlib

open Set
open scoped ENNReal
noncomputable section
namespace OAI.Geometry.Nikodym

/-- A continuous average maximized over a compact, closed admissibility
relation is upper semicontinuous. This allows closed incidence and length
conditions, not just open admissibility conditions. -/
theorem upperSemicontinuous_compact_admissible_sup
    {P I : Type*} [TopologicalSpace P] [TopologicalSpace I] [CompactSpace I]
    (A : Set (P × I)) (hA : IsClosed A) (f : P × I → ℝ≥0∞) (hf : Continuous f) :
    UpperSemicontinuous (fun p => ⨆ i, ⨆ (_ : (p,i) ∈ A), f (p,i)) := by
  classical
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro c
  by_cases hc : c=0
  · subst c
    convert isClosed_univ using 1
    ext p
    simp
  have he : (fun p => ⨆ i, ⨆ (_ : (p,i) ∈ A), f (p,i)) ⁻¹' Ici c =
      Prod.fst '' (A ∩ f ⁻¹' Ici c) := by
    ext p
    constructor
    · intro hp
      change c ≤ ⨆ i,⨆ (_ : (p,i)∈A),f (p,i) at hp
      have hne : {i : I | (p,i)∈A}.Nonempty := by
        by_contra hn
        have hh : ∀ i : I,(p,i)∉A := by
          simpa only [Set.nonempty_def,not_exists,Set.mem_ofPred_eq] using hn
        have hz : (⨆ i,⨆ (_ : (p,i)∈A),f (p,i))=0 := by simp [hh]
        exact hc (le_antisymm (hz ▸ hp) bot_le)
      have hcl : IsClosed {i : I | (p,i)∈A} :=
        hA.preimage (continuous_const.prodMk continuous_id)
      have hfc : Continuous (fun i : I => f (p,i)) :=
        hf.comp (continuous_const.prodMk continuous_id)
      obtain ⟨i,hi,hmax⟩ := hfc.continuousOn.upperSemicontinuousOn.exists_isMaxOn
        hne hcl.isCompact
      refine ⟨(p,i),⟨hi,?_⟩,rfl⟩
      exact hp.trans (iSup_le fun j => iSup_le fun hj =>
        (show f (p,j) ≤ f (p,i) from hmax hj))
    · rintro ⟨⟨q,i⟩,⟨hi,hci⟩,rfl⟩
      change c ≤ ⨆ j,⨆ (_ : (q,j)∈A),f (q,j)
      exact hci.trans (le_iSup_of_le i (le_iSup_of_le hi le_rfl))
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ (hA.inter (isClosed_Ici.preimage hf))

theorem measurable_compact_admissible_sup
    {P I : Type*} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace I] [CompactSpace I]
    (A : Set (P × I)) (hA : IsClosed A) (f : P × I → ℝ≥0∞) (hf : Continuous f) :
    Measurable (fun p => ⨆ i, ⨆ (_ : (p,i) ∈ A), f (p,i)) :=
  (upperSemicontinuous_compact_admissible_sup A hA f hf).measurable

end OAI.Geometry.Nikodym
