import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBankBounds

namespace OAI.Algorithms

/-! Matrix-image generation charged to the same actual enumeration arrays
whose records the node consumes.  The array equality fixes representation
and order; the numeric count bound follows internally. -/

namespace SubexponentialSAT.SubexpNodeBankRuntimeBound

open scoped BigOperators
open SubexpNodeBankMap SubexpNodeBankBounds Subexp.MatrixWordEncoding

def scale (p D : ℕ) [Fact p.Prime] : ℕ := commonSize p D + D + width p + 1

private theorem matrix_caps {p D : ℕ} [Fact p.Prime]
    (M : Matrix p D) (J : ℕ) (hJ : 1 ≤ J) (hc : p^M.columns ≤ J)
    (hn : M.columns+1 ≤ J) :
    (payload M).length ≤ 10*(scale p D)^2*J ∧
    (bankList M).length ≤ 5*(scale p D)^2*J ∧
    Subexp.MatrixImageEnumeration.sourceBudget p M.entries ≤
      50000*(scale p D)^3*J^3 := by
  let S := scale p D
  have hS : 1 ≤ S := by dsimp [S, scale]; omega
  have hD : D+1 ≤ S := by dsimp [S, scale]; omega
  have hw : width p+1 ≤ S := by dsimp [S, scale]; omega
  have hDS : D ≤ S := by omega
  have hnJ : M.columns ≤ J := by omega
  have hf : 2*width p+1 ≤ 3*S := by omega
  have hmat : (Subexp.BlockCoefficientProgram.matrixBits p M.entries).length ≤ 3*S^2*J := by
    rw [Subexp.MatrixImageEnumeration.matrixBits_length]
    calc
      _ ≤ S*J*(3*S) := Nat.mul_le_mul (Nat.mul_le_mul hDS hnJ) hf
      _ = _ := by ring
  have hSJ : J ≤ S^2*J := by
    simpa only [one_mul] using Nat.mul_le_mul_right J (Nat.one_le_pow 2 S hS)
  have hlen : (payload M).length = 2*M.columns+
      2*(Subexp.BlockCoefficientProgram.matrixBits p M.entries).length+2 := by
    simp [payload, Encoding.length_frame]
    omega
  have hpay : (payload M).length ≤ 10*S^2*J := by
    rw [hlen]
    nlinarith only [hmat, hnJ, hSJ, hJ]
  have hDw : D*width p ≤ S^2 := by
    calc
      _ ≤ S*S := Nat.mul_le_mul hDS (by omega)
      _ = _ := by ring
  have hcoef : 2*(D*width p)+2 ≤ 4*S^2 := by nlinarith only [hDw, hS]
  have hbank : (bankList M).length ≤ 5*S^2*J := by
    rw [bankList, Subexp.MatrixImageEnumeration.output_length]
    have hp := Nat.mul_le_mul hcoef hc
    nlinarith only [hp, hSJ, hJ]
  have hsource : Subexp.MatrixImageEnumeration.sourceBudget p M.entries ≤ 50000*S^3*J^3 := by
    apply (Subexp.MatrixImageEnumeration.sourceBudget_le p M.entries).trans
    calc
      _ ≤ 50000*S*J^2*S^2*J := by gcongr
      _ = _ := by ring
  exact ⟨hpay, hbank, hsource⟩

private theorem runtime_le {p D : ℕ} [Fact p.Prime]
    (matrices : List (Matrix p D)) (J : ℕ) (hJ : 1 ≤ J)
    (hlen : matrices.length ≤ J)
    (hcount : ∀ M ∈ matrices, p^M.columns ≤ J)
    (hcolumns : ∀ M ∈ matrices, M.columns+1 ≤ J) :
    runtimeBound matrices ≤ 100000*(scale p D)^3*J^4 := by
  let S := scale p D
  have hS : 1 ≤ S := by dsimp [S, scale]; omega
  have hc : commonSize p D ≤ S := by dsimp [S, scale]; omega
  have hcaps := fun M hM => matrix_caps M J hJ (hcount M hM) (hcolumns M hM)
  have hb := runtimeBound_le matrices (10*S^2*J) (5*S^2*J) (50000*S^3*J^3)
    (fun M hM => (hcaps M hM).1) (fun M hM => (hcaps M hM).2.1)
    (fun M hM => (hcaps M hM).2.2)
  have hu : runtimeBound matrices ≤
      50000*(S^3*J^4)+450*(S^2*J^2)+60*J+9*S+50 := by
    calc
      _ ≤ 9*S+50+J*(50000*S^3*J^3+31*(10*S^2*J)+28*(5*S^2*J)+60) :=
        hb.trans (by gcongr)
      _ = _ := by ring
  have hv : S^2*J^2 ≤ S^3*J^4 := Nat.mul_le_mul
    (Nat.pow_le_pow_right hS (by decide)) (Nat.pow_le_pow_right hJ (by decide))
  have hsK : S ≤ S^3*J^4 := by
    calc
      S = S*1 := by omega
      _ ≤ S^3*J^4 := Nat.mul_le_mul (Nat.le_self_pow (by decide) S) (Nat.one_le_pow 4 J hJ)
  have hjK : J ≤ S^3*J^4 := by
    calc
      J = 1*J := by omega
      _ ≤ S^3*J^4 := Nat.mul_le_mul (Nat.one_le_pow 3 S hS) (Nat.le_self_pow (by decide) J)
  have hfinal : runtimeBound matrices ≤ 100000*(S^3*J^4) := by omega
  simpa only [Nat.mul_assoc] using hfinal

section Layout

variable {p D k Δ r : ℕ} {τ : ℚ} [Fact p.Prime]
variable {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
variable {P : Factor.Pattern (Fin D) F} {c : SubexpLayoutSpec.Parameters p k Δ r τ}
variable {L : SubexpLayoutSpec.Layout (E := E) P c} {t : Fin c.Q}

/-- The physical matrix bank arrays agree with the proved layout arrays.
Their output count and the complete enumerator cost are then derived. -/
theorem runtimeBound_le_iterations (e : SubexpLayoutSpec.EnumerationData L t)
    (matrices : List (Matrix p D))
    (harrays : matrices.map (fun M => Subexp.MatrixImageEnumeration.bankRecords p M.entries) =
      outerBanks e :: innerBanks e) :
    runtimeBound matrices ≤ 100000*(scale p D)^3*(e.iterationCount+1)^4 := by
  have hlen : matrices.length ≤ e.iterationCount+1 := by
    have h := congrArg List.length harrays
    simp only [List.length_map, List.length_cons, innerBanks, List.length_ofFn] at h
    have hr := colors_le_iterations e
    omega
  have hcount : ∀ M ∈ matrices, p^M.columns ≤ e.iterationCount := by
    intro M hM
    have hm : Subexp.MatrixImageEnumeration.bankRecords p M.entries ∈ outerBanks e :: innerBanks e := by
      rw [← harrays]
      exact List.mem_map.mpr ⟨M, hM, rfl⟩
    rcases List.mem_cons.mp hm with he | hi
    · have h := congrArg List.length he
      simp only [Subexp.MatrixImageEnumeration.bankRecords_length, outerBanks, bank_length] at h
      exact h.trans_le (outerCount_le_iterations e)
    · obtain ⟨g, hg⟩ := List.mem_ofFn.mp hi
      have h := congrArg List.length hg
      simp only [Subexp.MatrixImageEnumeration.bankRecords_length, bank_length] at h
      have hgSum : e.innerCount g ≤ ∑ j, e.innerCount j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
      exact h.symm.trans_le (hgSum.trans (innerSum_le_iterations e))
  apply runtime_le matrices (e.iterationCount+1) (by omega) hlen
  · intro M hM; exact (hcount M hM).trans (Nat.le_succ _)
  · intro M hM
    have hp : M.columns < p^M.columns := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
    have hc := hcount M hM
    omega

end Layout

end SubexponentialSAT.SubexpNodeBankRuntimeBound

end OAI.Algorithms
