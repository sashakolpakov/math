import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.FamilyGap
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.WordMinors

/-! # Word Minor Gap -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.WordMinorGap.Construction

noncomputable section

/-! Uniform vector gaps for nonzero discrete word minors in a compact
family of matrix operators. -/

open scoped Classical

theorem compact_matrix_family_word_minor_gap
    {R ι : Type*} [NormedCommRing R] [Fintype ι] {n d : ℕ}
    (K : Set (ι → Matrix (Fin n) (Fin n) R)) (hK : IsCompact K)
    (D : Set R) (hD : IsDiscrete D) (hD0 : (0 : R) ∈ D) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ A ∈ K, ∀ x : Fin n → R,
      (∃ q : Finite.WordMinors.Construction.boundedWordMinorIndex ι n d, Finite.WordMinors.Construction.boundedWordMinor q A x ∈ D ∧
        Finite.WordMinors.Construction.boundedWordMinor q A x ≠ 0) → ε ≤ ‖x‖ := by
  have hq (q : Finite.WordMinors.Construction.boundedWordMinorIndex ι n d) :=
    Compact.FamilyGap.Construction.uniform_gap_of_compact_family_discrete_values K hK
      (fun p => Finite.WordMinors.Construction.boundedWordMinor q p.1 p.2) (Finite.WordMinors.Construction.continuous_boundedWordMinor q)
      (fun A _ => Finite.WordMinors.Construction.boundedWordMinor_zero q A) D hD hD0
  choose ε hε hgap using hq
  let s : Finset ℝ := insert 1 (Finset.univ.image ε)
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  have hpos : 0 < s.min' hs := by
    apply (Finset.lt_min'_iff _ _).mpr
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · norm_num
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
      exact hε q
  refine ⟨s.min' hs, hpos, fun A hA x hx => ?_⟩
  obtain ⟨q, hqD, hq0⟩ := hx
  exact (Finset.min'_le s (ε q) (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩))).trans (hgap q A hA x hqD hq0)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.WordMinorGap.Construction
