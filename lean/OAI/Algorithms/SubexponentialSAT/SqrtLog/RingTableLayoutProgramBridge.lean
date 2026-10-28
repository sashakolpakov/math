import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayoutProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTripleBridge

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.SubexpQuarticRing

/-- The input is power-major: all coefficients of P0, then P1, and so on. -/
def powerRecords {d B : ℕ} (P : ℕ → Fin d → Word B) (n : ℕ) : List (List Bool) :=
  (List.ofFn fun a : Fin n => List.ofFn fun k : Fin d => (P a.val k).val).flatten

theorem powerRecords_eq_ofFn {d B : ℕ} (P : ℕ → Fin d → Word B) (n : ℕ) :
    powerRecords P n =
      List.ofFn (fun x : Fin (n*d) => (P x.divNat.val x.modNat).val) := by
  rw [powerRecords, List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext a
  apply congrArg List.ofFn
  funext k
  have hd : 0 < d := (Nat.zero_le k.val).trans_lt k.isLt
  have hdiv : (a.val*d+k.val)/d = a.val := by
    rw [Nat.mul_comm a.val d, Nat.mul_add_div hd, Nat.div_eq_of_lt k.isLt]
    omega
  have hmod : (a.val*d+k.val)%d = k.val := by
    simp [Nat.mod_eq_of_lt k.isLt]
  simp only [Fin.divNat, Fin.modNat, hdiv]
  have hk : (⟨(a.val*d+k.val)%d, by omega⟩ : Fin d) = k := Fin.ext hmod
  simp only [hk]

@[simp] theorem powerRecords_length {d B : ℕ} (P : ℕ → Fin d → Word B) (n : ℕ) :
    (powerRecords P n).length = n*d := by simp [powerRecords_eq_ofFn]

theorem powerRecords_width {d B : ℕ} (P : ℕ → Fin d → Word B) (n : ℕ) :
    ∀ row ∈ powerRecords P n, row.length = B := by
  intro row hr
  rw [powerRecords_eq_ofFn] at hr
  obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hr
  exact (P x.divNat.val x.modNat).property

theorem powerRecords_lookup {d B n : ℕ} (P : ℕ → Fin d → Word B)
    (a : Fin n) (k : Fin d) :
    wordAt (powerRecords P n) (a.val*d+k.val) = (P a.val k).val := by
  have hb : a.val*d+k.val < n*d := by nlinarith [a.isLt, k.isLt]
  have hd : 0 < d := (Nat.zero_le k.val).trans_lt k.isLt
  have hdiv : (a.val*d+k.val)/d = a.val := by
    rw [Nat.mul_comm a.val d, Nat.mul_add_div hd, Nat.div_eq_of_lt k.isLt]
    omega
  have hmod : (a.val*d+k.val)%d = k.val := by simp [Nat.mod_eq_of_lt k.isLt]
  simp only [wordAt, powerRecords_eq_ofFn, getElem!_pos, List.length_ofFn, hb,
    List.getElem_ofFn, Fin.divNat, Fin.modNat, hdiv]
  have hk : (⟨(a.val*d+k.val)%d, by omega⟩ : Fin d) = k := Fin.ext hmod
  simp only [hk]

theorem power_layout_eq_tableEncoding {d B : ℕ} (P : ℕ → Fin d → Word B) :
    layoutBits (powerRecords P (2*d-1)) d 0 d =
      RingTriple.tableEncoding (fun i j k => P (i.val+j.val) k) := by
  rw [layoutBits_eq_ofFn, RingTriple.tableEncoding]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext k
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  have ha : i.val+j.val < 2*d-1 := by omega
  have hidx : 0+k.val+i.val*d+j.val*d = (i.val+j.val)*d+k.val := by ring
  rw [hidx]
  exact powerRecords_lookup P ⟨i.val+j.val, ha⟩ k

/-- The consumer ABI is exactly RingTriple.tableEncoding, including every
zero coefficient and the k-major/i-next/j-fastest ordering. -/
theorem power_table_program_run {d B : ℕ} (P : ℕ → Fin d → Word B)
    (degree width : List Bool) (regs : Fin 2 → Bool)
    (hd : degree.length = d) (hw : width.length = B) :
    ∃ rf, RunsIn program (budget d B + 1)
      ((state regs (initial (powerRecords P (2*d-1)).flatten degree width)).withPC
        (some program.entry))
      ((state rf {(initial (powerRecords P (2*d-1)).flatten degree width) with
        out := RingTriple.tableEncoding (fun i j k => P (i.val+j.val) k)}).withPC none) := by
  have h := program_run (powerRecords P (2*d-1)) degree width regs
    (by simpa only [hw] using powerRecords_width P (2*d-1))
    (by simp [hd, Nat.mul_comm])
  simpa only [hd, hw, power_layout_eq_tableEncoding] using h

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
