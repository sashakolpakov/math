import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramController

namespace OAI.Algorithms

/-! Dropping a candidate-independent offset is justified by an exact ordering
proof. The real controller remains unchanged, and its score builder must still
satisfy an actual execution contract. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

 theorem chooseMinNat_eq_of_order {A : Type*} (f g : A → ℕ)
    (h : ∀ a b, f a ≤ f b ↔ g a ≤ g b) (a : A) (tail : List A) :
    NaturalAssignment.chooseMinNat f a tail = NaturalAssignment.chooseMinNat g a tail := by
  induction tail generalizing a with
  | nil => rfl
  | cons b tail ih => simp only [NaturalAssignment.chooseMinNat, ih, h]

 theorem assignNat_eq_of_order {A : Type*} (a : A) (tail : List A)
    (f g : ℕ → List A → ℕ) (total : ℕ)
    (h : ∀ n fixed, n+1+fixed.length = total → ∀ x y,
      f n (x::fixed) ≤ f n (y::fixed) ↔ g n (x::fixed) ≤ g n (y::fixed))
    (n : ℕ) (fixed : List A) (hs : n+fixed.length = total) :
    NaturalAssignment.assignNat a tail f n fixed =
      NaturalAssignment.assignNat a tail g n fixed := by
  induction n generalizing fixed with
  | zero => rfl
  | succ n ih =>
    have ho := h n fixed (by omega)
    have hc := chooseMinNat_eq_of_order (fun x => f n (x::fixed))
      (fun x => g n (x::fixed)) ho a tail
    simp only [NaturalAssignment.assignNat, hc]
    apply ih
    simp only [List.length_cons]
    omega

section Controller
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SqrtLog.Packing
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

 omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
 theorem controller_runsIn_ordered (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (w : Weights)
    (evaluate : ℕ → List (Word r Q) → ℕ) (bound : ℕ)
    (horder : ∀ n fixed, n+1+fixed.length = indices.length → ∀ x y,
      evaluate n (x::fixed) ≤ evaluate n (y::fixed) ↔
      sequentialNumerator ivar factor (a::tail) terms indices w a n (x::fixed) ≤
      sequentialNumerator ivar factor (a::tail) terms indices w a n (y::fixed))
    (hbound : ∀ n fixed x, n+1+fixed.length ≤ indices.length → x ∈ a::tail →
      evaluate n (x::fixed) ≤ bound)
    (builder : Cmd 16 48) (cost : ℕ) (environment : Fin 48 → List Bool)
    (hproducer : SequentialProgram.ScoreBuilderRefines ReadPlan.encodeWord a tail
      evaluate builder cost indices.length environment)
    (d : SequentialProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail indices.length [] d.stacks)
    (hc : (d.stacks 11).length = indices.length)
    (he : SequentialProgram.HighState environment d.stacks) :
    ∃ e : SequentialProgram.Data,
      RunsIn (SequentialProgram.program builder)
        (indices.length*(cost+SequentialProgram.selectionBudget (a::tail).length bound
          indices.length (ReadPlan.encodeWord a).length+3)+3)
        (d.withPC (some (SequentialProgram.program builder).entry)) (e.withPC none) ∧
      e.stacks 8 = ((selectedValues ivar factor a tail terms indices w).reverse.map
        ReadPlan.encodeWord).flatten := by
  obtain ⟨e, hr, ho⟩ := SequentialProgram.program_of_scoreBuilder ReadPlan.encodeWord a tail
    evaluate builder cost bound indices.length environment
    (fun z => by simp [ReadPlan.encodeWord_length]) hbound hproducer d hm hc he
  refine ⟨e, hr, ?_⟩
  have hvalues := assignNat_eq_of_order a tail evaluate
    (sequentialNumerator ivar factor (a::tail) terms indices w a) indices.length horder
    indices.length [] (by simp)
  simpa only [hvalues, selectedValues] using ho
end Controller
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
