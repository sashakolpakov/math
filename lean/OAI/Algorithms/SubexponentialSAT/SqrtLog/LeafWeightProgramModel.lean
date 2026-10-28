import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsBoolean

namespace OAI.Algorithms

/-! The native three-mask branch computes the exact squarefree head weight. -/
namespace SubexponentialSAT.SqrtLog.LeafWeightProgram

open SubexponentialSAT
open scoped BigOperators

theorem good_ofFn_iff {n : ℕ} (a s h : Fin n → Bool) :
    good (List.ofFn a) (List.ofFn s) (List.ofFn h) = true ↔
      ∀ i, s i = true → h i = true → a i = true := by
  induction n with
  | zero => simp [good]
  | succ n ih =>
    cases ha : a 0 <;> cases hs : s 0 <;> cases hh : h 0 <;>
      simp [List.ofFn_succ,good,ha,hs,hh,ih,Fin.forall_fin_succ]

def supportBits {n : ℕ} (s : Squarefree.Support (Fin n)) : List Bool :=
  List.ofFn fun i => decide (i ∈ s.vars)
def headBits {n : ℕ} {G : Type*} [DecidableEq G] (head : Fin n → G) (g : G) : List Bool :=
  List.ofFn fun i => decide (head i = g)

theorem selected_iff {n : ℕ} {G : Type*} [DecidableEq G]
    (a : Fin n → Bool) (s : Squarefree.Support (Fin n)) (head : Fin n → G) (g : G) :
    good (List.ofFn a) (supportBits s) (headBits head g) = true ↔
      ∀ i ∈ s.vars, head i = g → a i = true := by
  simpa [supportBits,headBits] using
    good_ofFn_iff a (fun i => decide (i ∈ s.vars)) (fun i => decide (head i = g))

/-- This also covers empty ambient sets and empty support intersections. -/
theorem localBoolWeight_eq {n : ℕ} {G R : Type*} [Fintype G] [DecidableEq G]
    [CommSemiring R] (a : Fin n → Bool) (s : Squarefree.Support (Fin n))
    (head : Fin n → G) (g : G) :
    (if good (List.ofFn a) (supportBits s) (headBits head g) then (1:R) else 0) =
      Moments.localBoolWeight head s g (fun i => a i.val) := by
  classical
  have hc := selected_iff a s head g
  cases hg : good (List.ofFn a) (supportBits s) (headBits head g) with
  | false =>
    have hn : ¬ ∀ i ∈ s.vars, head i = g → a i = true := by
      intro hh
      have he := hc.mpr hh
      rw [hg] at he
      contradiction
    push Not at hn
    obtain ⟨i,hi,hhead,ha⟩ := hn
    have ha' : a i = false := by cases hx : a i <;> simp_all
    have hp : Moments.localBoolWeight (R:=R) head s g (fun i => a i.val) = 0 := by
      unfold Moments.localBoolWeight
      exact Finset.prod_eq_zero hi (by simp [hhead,ha'])
    simpa [hg] using hp.symm
  | true =>
    have hh := hc.mp hg
    simp only [ ↓reduceIte]
    symm
    unfold Moments.localBoolWeight
    apply Finset.prod_eq_one
    intro i hi
    by_cases hhead : head i = g
    · simp [hhead,hh i hi hhead]
    · simp [hhead]

/-- Supplying the actual encoded zero and one is sufficient: the executed
branch, rather than a semantic weight callback, chooses the correct word. -/
theorem result_decode {n : ℕ} {G R : Type*} [Fintype G] [DecidableEq G]
    [CommSemiring R] (decode : List Bool → R) (zero one : List Bool)
    (hzero : decode zero = 0) (hone : decode one = 1)
    (a : Fin n → Bool) (s : Squarefree.Support (Fin n)) (head : Fin n → G) (g : G) :
    decode (Native.result (List.ofFn a) (supportBits s) (headBits head g) zero one) =
      Moments.localBoolWeight head s g (fun i => a i.val) := by
  rw [← localBoolWeight_eq a s head g]
  cases hg : good (List.ofFn a) (supportBits s) (headBits head g) <;>
    simp [Native.result,hg,hzero,hone]

/-- One complete physical execution, including preservation of all five
masters, returns the exact local Boolean weight at its measured bit cost. -/
theorem program_localBoolWeight {n : ℕ} {G R : Type*} [Fintype G] [DecidableEq G]
    [CommSemiring R] (decode : List Bool → R) (zero one : List Bool) (W : ℕ)
    (hzero : decode zero = 0) (hone : decode one = 1)
    (hz : zero.length = W) (ho : one.length = W) (r : Fin 8 → Bool)
    (a : Fin n → Bool) (s : Squarefree.Support (Fin n)) (head : Fin n → G) (g : G) :
    ∃ rf out, BitProgram.Trace Native.program (29*n+7*W+26)
      ((Native.data r (List.ofFn a) (supportBits s) (headBits head g)
        zero one [] [] [] []).withPC (some Native.program.entry))
      ((Native.data rf (List.ofFn a) (supportBits s) (headBits head g)
        zero one [] [] [] out).withPC none) ∧
      decode out = Moments.localBoolWeight head s g (fun i => a i.val) ∧
      out.length = W := by
  have hl := Native.result_length (List.ofFn a) (supportBits s) (headBits head g)
    zero one W hz ho
  obtain ⟨rf,he⟩ := Native.program_trace r (List.ofFn a) (supportBits s)
    (headBits head g) zero one (by simp [supportBits]) (by simp [headBits])
  refine ⟨rf, Native.result (List.ofFn a) (supportBits s) (headBits head g) zero one,
    ?_, result_decode decode zero one hzero hone a s head g, hl⟩
  simpa only [List.length_ofFn, hl] using he

end SubexponentialSAT.SqrtLog.LeafWeightProgram

end OAI.Algorithms
