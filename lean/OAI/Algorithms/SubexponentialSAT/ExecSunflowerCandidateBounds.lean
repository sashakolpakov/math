import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerCandidateProgram
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerCandidateSpec

namespace OAI.Algorithms

/-! Mathematical validity and a uniform polynomial bound for the actual
candidate instruction sequence. -/

namespace SubexponentialSAT.ExecSunflowerCandidateProgram

theorem accepted_sunflower (G : Formula) (H : Clause) (width size : List Bool)
    (ha : answer G H width size = true) :
    Sunflower.IsSunflowerWithCore (ExecCNF.formulaSet G) (ExecCNF.clauseSet H) := by
  obtain ⟨⟨⟨_, hc⟩, hp⟩, _⟩ := (answer_true_iff G H width size).mp ha
  exact ExecSunflowerCandidateSpec.isSunflower_of_checks G H hc
    ((ExecSunflowerPairScan.AllPairs.no_badPairs_iff H G).mpr hp)

theorem accepted_normalized (G : Formula) (H : Clause) (width size : List Bool)
    (ha : answer G H width size = true)
    (hG : (G.map ExecCNF.clauseSet).Nodup) (hC : ∀ C ∈ G, C.Nodup) :
    (ExecCNF.clauseSet H).Nonempty ∧
      Sunflower.IsSunflowerWithCore (ExecCNF.formulaSet G) (ExecCNF.clauseSet H) ∧
      (ExecCNF.formulaSet G).card = BinaryArithmetic.toNat size ∧
      ∀ C ∈ ExecCNF.formulaSet G, C.card = BinaryArithmetic.toNat width := by
  obtain ⟨⟨⟨⟨hs, hw⟩, _⟩, _⟩, hne⟩ := (answer_true_iff G H width size).mp ha
  refine ⟨?_, accepted_sunflower G H width size ha,
    (ExecSunflowerCandidateSpec.selected_card G hG).trans hs,
    ExecSunflowerCandidateSpec.selected_uniform G _ hC hw⟩
  cases H with
  | nil => exact False.elim (hne rfl)
  | cons x xs => exact ⟨x, by simp⟩

/-- A polynomial in actual encoded input sizes, with no inference from a
decoded integer's value to the length of an arbitrarily padded bit word. -/
theorem bound_le_uniform (G : Formula) (H : Clause) (width size : List Bool) (B : ℕ)
    (hG : (Encoding.encodeList (Encoding.encodeList id) G).length ≤ B)
    (hH : (Encoding.encodeList id H).length ≤ B)
    (hw : width.length ≤ B) (hs : size.length ≤ B) :
    bound G H width size ≤ 8192 * (B + 1)^4 := by
  let b := B + 1
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hg1 : (Encoding.encodeList (Encoding.encodeList id) G).length + 1 ≤ b := by
    dsimp [b]; omega
  have hh1 : (Encoding.encodeList id H).length + 1 ≤ b := by dsimp [b]; omega
  have hh3 : (Encoding.encodeList id H).length + 3 ≤ 3 * b := by dsimp [b]; omega
  have hgw : (Encoding.encodeList (Encoding.encodeList id) G).length + width.length + 1 ≤ 2 * b := by
    dsimp [b]; omega
  have hgs : (Encoding.encodeList (Encoding.encodeList id) G).length + size.length + 1 ≤ 2 * b := by
    dsimp [b]; omega
  have hg : (Encoding.encodeList (Encoding.encodeList id) G).length ≤ b := by omega
  have hcoarse : bound G H width size ≤
      200 * (2 * b)^2 + (300 * (2 * b)^2 + 17) * b + 16 * b + 30 +
      512 * b * b + (4 + (1024 * (3 * b) + 70) * b^3 + 9 * b + 8) + 13 := by
    unfold bound FamilySizeGuardProgram.bound ExecClauseRelationScan.Preserving.bound
      PairCall.bound ExecSunflowerPairScan.AllPairs.polynomialBound
    unfold FamilySizeGuardProgram.familyCode FamilySizeGuardProgram.clauseCode
      ExecClauseRelationScan.encodeClause ExecClauseRelationScan.encodeFormula
    gcongr ; assumption
  have hb2 : b ≤ b^2 := by nlinarith
  have hb3 : b^2 ≤ b^3 := by nlinarith
  have hb4 : b^3 ≤ b^4 := by nlinarith
  have hone : 1 ≤ b^4 := by omega
  change _ ≤ 8192 * b^4
  nlinarith

end SubexponentialSAT.ExecSunflowerCandidateProgram

end OAI.Algorithms
