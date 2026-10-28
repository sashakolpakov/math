import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramPreprocessMatrix

namespace OAI.Algorithms

/-! Integer semantics and explicit polynomial bounds for the concrete
signed-coefficient preprocessing machine. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp.MatrixProgramSupport

def preWordsBounded (L : ℕ) (xs : List SignedWord) : Prop :=
  ∀ a∈xs, a.1.length ≤ L ∧ a.2.length ≤ L

theorem shiftedWords_length_bound {W : List Bool} {xs : List SignedWord}
    {ys : List (List Bool)} (h : List.Forall₂ (shiftedWord W) xs ys)
    (L : ℕ) (hW : W.length ≤ L) (hb : preWordsBounded L xs) :
    ∀ y∈ys, y.length ≤ 3*L+1 := by
  induction h with
  | nil => simp
  | @cons a y xs ys hy hys ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · have ha := hb a (by simp)
        have hh := hy.2
        omega
      · exact ih (fun a ha => hb a (by simp [ha])) z hz

theorem shiftedMatrix_rowWidth {W : List Bool} {xs : List (List SignedWord)}
    {ys : List (List (List Bool))} (h : List.Forall₂ (List.Forall₂ (shiftedWord W)) xs ys)
    (width : ℕ) (hw : ∀ row∈xs, row.length=width) :
    ∀ row∈ys, row.length=width := by
  induction h with
  | nil => simp
  | @cons a y xs ys hy hys ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact (shiftedWords_length hy).symm.trans (hw a (by simp))
      · exact ih (fun a ha => hw a (by simp [ha])) z hz

theorem shiftedWords_integer {W : List Bool} {xs : List SignedWord} {ys : List (List Bool)}
    (h : List.Forall₂ (shiftedWord W) xs ys)
    (hb : ∀ a∈xs, SubexponentialSAT.BinaryArithmetic.toNat a.2 ≤ SubexponentialSAT.BinaryArithmetic.toNat W) :
    List.Forall₂ (fun a y => (SubexponentialSAT.BinaryArithmetic.toNat y : ℤ) =
      (SubexponentialSAT.BinaryArithmetic.toNat W : ℤ)+
        ((SubexponentialSAT.BinaryArithmetic.toNat a.1 : ℤ)-(SubexponentialSAT.BinaryArithmetic.toNat a.2 : ℤ))) xs ys := by
  induction h with
  | nil => exact .nil
  | @cons a y xs ys h hs ih =>
      exact .cons (shiftedWord_integer W a y h (hb a (by simp)))
        (ih (fun z hz => hb z (by simp [hz])))

theorem preStepCost_le (W : List Bool) (a : SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hP : a.1.length ≤ L) (hN : a.2.length ≤ L) :
    preStepCost W a ≤ 6000*(L+1)^2 := by
  have hsum : W.length+a.2.length+a.1.length+1 ≤ 3*L+1 := by omega
  have hsq := Nat.pow_le_pow_left hsum 2
  dsimp [preStepCost]
  nlinarith

theorem preRow_inputs (W : List Bool) (xs : List SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hb : preWordsBounded L xs) :
    preScanCost W xs ≤ (xs.length+1)*(6000*(L+1)^2+2) ∧
    preOutputLength W xs ≤ xs.length*(3*L+1) ∧
    (signedWords xs).length ≤ xs.length*(4*L+2) := by
  induction xs with
  | nil => simp [preScanCost,preOutputLength,signedWords]
  | cons a xs ih =>
      have ha := hb a (by simp)
      have ht := ih (fun x hx => hb x (by simp [hx]))
      have hc := preStepCost_le W a L hW ha.1 ha.2
      rcases a with ⟨P,N⟩
      simp only [preScanCost,preOutputLength,List.map_cons,List.sum_cons,
        List.length_cons,signedWords,List.length_append,Encoding.length_frame] at *
      constructor
      · nlinarith [ht.1]
      constructor
      · nlinarith [ht.2.1]
      · nlinarith [ht.2.2]

theorem preRowCost_le (W : List Bool) (xs : List SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hb : preWordsBounded L xs) :
    preRowCost W xs ≤ 7000*(xs.length+1)*(L+1)^2 := by
  have h := preRow_inputs W xs L hW hb
  have hlin : 3*L+1 ≤ 3*(L+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul_left xs.length hlin
  have hs : 1 ≤ (L+1)^2 := by nlinarith
  have hn := Nat.mul_le_mul_left xs.length hs
  dsimp [preRowCost]
  nlinarith [h.1,h.2.1]

theorem preMatrixStepCost_le (W : List Bool) (row : List SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hb : preWordsBounded L row) :
    preMatrixStepCost W row ≤ 8000*(row.length+1)*(L+1)^2 := by
  have h := preRow_inputs W row L hW hb
  have hr := preRowCost_le W row L hW hb
  have hlin : 4*L+2 ≤ 4*(L+1)^2 := by nlinarith
  have hlin' : 3*L+1 ≤ 3*(L+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul_left row.length hlin
  have hh' := Nat.mul_le_mul_left row.length hlin'
  have hs : 1 ≤ (L+1)^2 := by nlinarith
  have hn := Nat.mul_le_mul_left row.length hs
  dsimp [preMatrixStepCost]
  nlinarith [h.2.1,h.2.2]

theorem preMatrix_inputs (W : List Bool) (rows : List (List SignedWord)) (L h : ℕ)
    (hW : W.length ≤ L)
    (hb : ∀ row∈rows, preWordsBounded L row ∧ row.length ≤ h) :
    preMatrixScanCost W rows ≤ (rows.length+1)*(8000*(h+1)*(L+1)^2+2) ∧
    preMatrixPayload W rows ≤ rows.length*(2*h*(3*L+1)+h) := by
  induction rows with
  | nil => simp [preMatrixScanCost,preMatrixPayload]
  | cons row rows ih =>
      have hr := hb row (by simp)
      have ht := ih (fun r hr' => hb r (by simp [hr']))
      have hc := preMatrixStepCost_le W row L hW hr.1
      have hc' : preMatrixStepCost W row ≤ 8000*(h+1)*(L+1)^2 :=
        hc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
      have hl := (preRow_inputs W row L hW hr.1).2.1
      have hl' := Nat.mul_le_mul_right (3*L+1) hr.2
      simp only [preMatrixScanCost,preMatrixPayload,List.map_cons,List.sum_cons,List.length_cons] at *
      constructor
      · nlinarith [ht.1]
      · nlinarith [ht.2]

theorem preMatrixCost_polynomial (W : List Bool) (rows : List (List SignedWord)) (L h : ℕ)
    (hW : W.length ≤ L)
    (hb : ∀ row∈rows, preWordsBounded L row ∧ row.length ≤ h) :
    preMatrixCost W rows+1 ≤ 10000*(rows.length+1)*(h+1)*(L+1)^2 := by
  have hi := preMatrix_inputs W rows L h hW hb
  have hlin : 3*L+1 ≤ 3*(L+1)^2 := by nlinarith
  have hp := Nat.mul_le_mul_left (rows.length*(2*h)) hlin
  have hs : 1 ≤ (L+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul_left (rows.length*h) hs
  have hn := Nat.mul_le_mul_left rows.length hs
  have hz := Nat.mul_le_mul_left h hs
  dsimp [preMatrixCost]
  nlinarith [hi.1,hi.2]

theorem preMatrixProgram_runsIn_polynomial (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) (L h : ℕ) (hW : W.length ≤ L)
    (hb : ∀ row∈rows, preWordsBounded L row ∧ row.length ≤ h) :
    ∃ rf ys, RunsIn preMatrixProgram (10000*(rows.length+1)*(h+1)*(L+1)^2)
      ((preMatrixState regs W rows []).withPC (some preMatrixProgram.entry))
      ((preMatrixState rf W [] (words (ys.map words))).withPC none) ∧
      List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys := by
  obtain ⟨rf,ys,⟨t,ht,he⟩,hy⟩ := preMatrixProgram_runsIn regs W rows
  exact ⟨rf,ys,⟨t,ht.trans (preMatrixCost_polynomial W rows L h hW hb),he⟩,hy⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
