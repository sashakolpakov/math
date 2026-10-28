import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramSignature

namespace OAI.Algorithms

/-! Equality of the complete physical key is equality of every original
integer constraint value. Framing introduces no collisions. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram
open SubexponentialSAT.Subexp.MatrixProgramSupport

theorem words_injective : Function.Injective words := by
  intro xs
  induction xs with
  | nil =>
      intro ys he
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hl := congrArg List.length he
          simp [words,Encoding.length_frame] at hl ; omega
  | cons x xs ih =>
      intro ys he
      cases ys with
      | nil =>
          have hl := congrArg List.length he
          simp [words,Encoding.length_frame] at hl
      | cons y ys =>
          obtain ⟨hxy,ht⟩ := Encoding.frame_append_injective he
          rw [hxy,ih ht]

theorem signatureValue_exact_iff {h k : ℕ} (W : List Bool)
    (c : Fin k → Fin h → List Bool) (A : Fin k → Fin h → ℤ)
    (x y : Fin h → Bool)
    (hc : ∀ j i, (SubexponentialSAT.BinaryArithmetic.toNat (c j i) : ℤ) =
      (SubexponentialSAT.BinaryArithmetic.toNat W : ℤ)+A j i) :
    signatureValue W (List.ofFn x) (List.ofFn (fun j => List.ofFn (c j))) =
      signatureValue W (List.ofFn y) (List.ofFn (fun j => List.ofFn (c j))) ↔
    ∀ j, (∑ i, A j i*(if x i then 1 else 0)) =
      (∑ i, A j i*(if y i then 1 else 0)) := by
  unfold signatureValue
  rw [words_injective.eq_iff,List.reverse_inj]
  simp only [List.map_ofFn]
  rw [List.ofFn_injective.eq_iff]
  constructor
  · intro he j
    exact (rowKey_exact_iff W (c j) (A j) x y (hc j)).mp (congrFun he j)
  · intro he
    funext j
    exact (rowKey_exact_iff W (c j) (A j) x y (hc j)).mpr (he j)

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
