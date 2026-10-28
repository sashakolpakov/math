import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerPairScan
import OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan
import OAI.Algorithms.SubexponentialSAT.Sunflower

namespace OAI.Algorithms

/-! Semantic interface for the actual encoded candidate checks. -/

namespace SubexponentialSAT.ExecSunflowerCandidateSpec

abbrev Clause := List (List Bool)
abbrev Formula := List Clause

open SubexpSunflowerProgram.Intersection

theorem containsIntersection_symm {C D H : Clause}
    (h : ContainsIntersection C D H) : ContainsIntersection D C H := by
  intro x hxD hxC
  exact h x hxC hxD

theorem pairwise_intersection_of_mem {G : Formula} {H C D : Clause}
    (h : G.Pairwise (fun C D => ContainsIntersection C D H))
    (hC : C ∈ G) (hD : D ∈ G) (hne : C ≠ D) : ContainsIntersection C D H := by
  induction G with
  | nil => simp at hC
  | cons E G ih =>
      rw [List.pairwise_cons] at h
      rcases List.mem_cons.mp hC with hCE | hCG
      · subst C
        rcases List.mem_cons.mp hD with hDE | hDG
        · exact False.elim (hne hDE.symm)
        · exact h.1 D hDG
      · rcases List.mem_cons.mp hD with hDE | hDG
        · subst D
          exact containsIntersection_symm (h.1 C hCG)
        · exact ih h.2 hCG hDG

/-- Core containment and the actual strict-tail pair scan establish exact
common intersections, including the reverse inclusion into every clause. -/
theorem isSunflower_of_checks (G : Formula) (H : Clause)
    (hcore : ∀ C ∈ G, ExecCNF.subset H C = true)
    (hpairs : ExecSunflowerPairScan.AllPairs.badPairs H G = false) :
    Sunflower.IsSunflowerWithCore (ExecCNF.formulaSet G) (ExecCNF.clauseSet H) := by
  have hpair := (ExecSunflowerPairScan.AllPairs.no_badPairs_iff H G).mp hpairs
  constructor
  · intro C hC
    obtain ⟨D, hD, rfl⟩ := ExecCNF.mem_formulaSet.mp hC
    exact (ExecCNF.subset_true H D).mp (hcore D hD)
  · intro C hC D hD hne
    obtain ⟨A, hA, rfl⟩ := ExecCNF.mem_formulaSet.mp hC
    obtain ⟨B, hB, rfl⟩ := ExecCNF.mem_formulaSet.mp hD
    have hAB : A ≠ B := by
      intro heq
      exact hne (congrArg ExecCNF.clauseSet heq)
    have hcA := (ExecCNF.subset_true H A).mp (hcore A hA)
    have hcB := (ExecCNF.subset_true H B).mp (hcore B hB)
    have hp := pairwise_intersection_of_mem hpair hA hB hAB
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
      exact ExecCNF.mem_clauseSet.mpr (hp x (ExecCNF.mem_clauseSet.mp hxA)
        (ExecCNF.mem_clauseSet.mp hxB))
    · intro x hx
      exact Finset.mem_inter.mpr ⟨hcA hx, hcB hx⟩

/-- The core-scan output has the expected polarity: `false` means no clause
is missing a core literal. -/
theorem isSunflower_of_scanner_flags (G : Formula) (H : Clause)
    (hcore : G.any (fun C => ExecClauseRelationScan.test .missingCore C H) = false)
    (hpairs : ExecSunflowerPairScan.AllPairs.badPairs H G = false) :
    Sunflower.IsSunflowerWithCore (ExecCNF.formulaSet G) (ExecCNF.clauseSet H) := by
  apply isSunflower_of_checks G H
  · intro C hC
    have hh := List.any_eq_false.mp hcore C hC
    simpa [ExecClauseRelationScan.test] using hh
  · exact hpairs

/-- Distinct selected clause sets make a raw selected-count check agree with
the number of mathematical petals. -/
theorem selected_card (G : Formula) (hd : (G.map ExecCNF.clauseSet).Nodup) :
    (ExecCNF.formulaSet G).card = G.length := by
  simpa [ExecCNF.formulaSet] using List.toFinset_card_of_nodup hd

/-- Literal normalization is needed when a record-count check is used as a
semantic clause-width check. -/
theorem selected_uniform (G : Formula) (d : ℕ)
    (hd : ∀ C ∈ G, C.Nodup) (hw : ∀ C ∈ G, C.length = d) :
    ∀ C ∈ ExecCNF.formulaSet G, C.card = d := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := ExecCNF.mem_formulaSet.mp hC
  exact (List.toFinset_card_of_nodup (hd D hD)).trans (hw D hD)

end SubexponentialSAT.ExecSunflowerCandidateSpec

end OAI.Algorithms
