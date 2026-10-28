import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramTotalStream

namespace OAI.Algorithms

/-! A single cached scalar term: three parsed operands, three real signed
multiplications, and one real signed addition. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev termStep : Cmd 8 18 :=
  .seq initializeOne (.seq multiply (.seq parse (.seq multiply
    (.seq parse (.seq multiply accumulate)))))

def termGrowth (B : ℕ) : ℕ := 14*B+52
def termCost (A B : ℕ) : ℕ := 100000000*(A+B+4)^2

theorem termStep_eval (regs : Fin 8 → Bool) (acc x y z : WordPair)
    (rest : List WordPair) (A B : ℕ)
    (ha : pairLength acc ≤ A) (hx : pairLength x ≤ B)
    (hy : pairLength y ≤ B) (hz : pairLength z ≤ B) :
    ∃ t ≤ termCost A B, ∃ r result,
      Eval termStep t
        (state regs acc ([],[]) x (pairEncoding (y::z::rest)))
        (state r result ([],[]) ([],[]) (pairEncoding rest)) ∧
      pairValue result = pairValue acc + pairValue x*pairValue y*pairValue z ∧
      pairLength result ≤ A+termGrowth B := by
  have hi := initializeOne_eval regs acc x (pairEncoding (y::z::rest))
  obtain ⟨t₁,ht₁,r₁,w₁,he₁,hv₁,hl₁⟩ := multiply_eval
    (Function.update regs 0 true) acc one x (pairEncoding (y::z::rest))
  obtain ⟨r₂,_,hp₂⟩ := parse_cons r₁ acc w₁ y (z::rest)
  obtain ⟨t₂,ht₂,r₃,w₂,he₂,hv₂,hl₂⟩ := multiply_eval r₂ acc w₁ y
    (pairEncoding (z::rest))
  obtain ⟨r₄,_,hp₃⟩ := parse_cons r₃ acc w₂ z rest
  obtain ⟨t₃,ht₃,r₅,w₃,he₃,hv₃,hl₃⟩ := multiply_eval r₄ acc w₂ z
    (pairEncoding rest)
  obtain ⟨t₄,ht₄,r₆,result,he₄,hv₄,hl₄⟩ := accumulate_eval r₅ acc w₃
    (pairEncoding rest)
  have hw₁ : pairLength w₁ ≤ 2*B+8 := by simp only [one_length] at hl₁; omega
  have hw₂ : pairLength w₂ ≤ 6*B+22 := by omega
  have hw₃ : pairLength w₃ ≤ 14*B+50 := by omega
  refine ⟨2+(t₁+((6*pairLength y+11)+(t₂+((6*pairLength z+11)+(t₃+t₄))))),
    ?_,r₆,result,hi.seq (he₁.seq (hp₂.seq (he₂.seq (hp₃.seq (he₃.seq he₄))))),?_,?_⟩
  · let H := A+14*B+53
    have h₁ : pairLength one+pairLength x+3 ≤ H := by simp only [one_length]; dsimp [H]; omega
    have h₂ : pairLength w₁+pairLength y+3 ≤ H := by dsimp [H]; omega
    have h₃ : pairLength w₂+pairLength z+3 ≤ H := by dsimp [H]; omega
    have h₄ : pairLength acc+pairLength w₃+3 ≤ H := by dsimp [H]; omega
    have ht₁' := ht₁.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 25000 (Nat.pow_le_pow_left h₁ 2)) 2)
    have ht₂' := ht₂.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 25000 (Nat.pow_le_pow_left h₂ 2)) 2)
    have ht₃' := ht₃.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 25000 (Nat.pow_le_pow_left h₃ 2)) 2)
    have ht₄' := ht₄.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 25000 (Nat.pow_le_pow_left h₄ 2)) 2)
    have hH : H ≤ 14*(A+B+4) := by dsimp [H]; omega
    have hsq := Nat.pow_le_pow_left hH 2
    let M := A+B+4
    have hMB : B+4 ≤ M := by dsimp [M]; omega
    have hMpos : 4 ≤ M := by omega
    have hlin : 12*B+32 ≤ 100*M^2 := by nlinarith only [hMB,hMpos]
    have htime : 2+(t₁+((6*pairLength y+11)+(t₂+
        ((6*pairLength z+11)+(t₃+t₄))))) ≤ 100000*H^2+12*B+32 := by
      omega
    have hsq' : H^2 ≤ 196*M^2 := by
      calc
        H^2 ≤ (14*(A+B+4))^2 := hsq
        _ = 196*M^2 := by dsimp [M]; ring
    change 2+(t₁+((6*pairLength y+11)+(t₂+
      ((6*pairLength z+11)+(t₃+t₄))))) ≤ 100000000*M^2
    omega
  · rw [hv₄,hv₃,hv₂,hv₁,one_value,one_mul]
  · dsimp [termGrowth]; omega

abbrev Triple := WordPair × WordPair × WordPair

def tripleWords (xs : List Triple) : List WordPair :=
  xs.flatMap fun x => [x.1,x.2.1,x.2.2]

def termValue (x : Triple) : ℤ :=
  pairValue x.1*pairValue x.2.1*pairValue x.2.2

def Bounded (B : ℕ) (xs : List Triple) : Prop :=
  ∀ x ∈ xs, pairLength x.1 ≤ B ∧ pairLength x.2.1 ≤ B ∧ pairLength x.2.2 ≤ B

abbrev scalarCommand : Cmd 8 18 :=
  .seq parse (.while 7 (.seq termStep parse))

def scalarCost : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 4
  | n+1, A, B => 6*B+11+termCost A B+scalarCost n (A+termGrowth B) B+1

theorem scalarCommand_eval (xs : List Triple) (regs : Fin 8 → Bool)
    (acc : WordPair) (A B : ℕ) (ha : pairLength acc ≤ A) (hx : Bounded B xs) :
    ∃ t ≤ scalarCost xs.length A B, ∃ r result,
      r 7 = false ∧
      Eval scalarCommand t
        (state regs acc ([],[]) ([],[]) (pairEncoding (tripleWords xs)))
        (state r result ([],[]) ([],[]) []) ∧
      pairValue result = pairValue acc+(xs.map termValue).sum ∧
      pairLength result ≤ A+xs.length*termGrowth B := by
  induction xs generalizing regs acc A with
  | nil =>
    obtain ⟨r,hg,he⟩ := parse_nil regs acc ([],[])
    refine ⟨4,le_rfl,r,acc,hg,he.seq (.while_false hg),?_,?_⟩
    · simp
    · simpa using ha
  | cons x xs ih =>
    have hb := hx x (by simp)
    have hxs : Bounded B xs := fun y hy => hx y (by simp [hy])
    obtain ⟨r₁,hg₁,hp⟩ := parse_cons regs acc ([],[]) x.1
      (x.2.1::x.2.2::tripleWords xs)
    obtain ⟨ts,hts,r₂,middle,hs,hv,hl⟩ := termStep_eval r₁ acc
      x.1 x.2.1 x.2.2 (tripleWords xs) A B ha hb.1 hb.2.1 hb.2.2
    obtain ⟨tt,htt,r₃,result,hg₃,ht,hv₃,hl₃⟩ :=
      ih r₂ middle (A+termGrowth B) hl hxs
    cases ht with
    | seq hn hw =>
      rename_i tn tw between
      refine ⟨6*pairLength x.1+11+(ts+tn+tw+1),?_,r₃,result,hg₃,?_,?_,?_⟩
      · simp only [scalarCost,List.length_cons] at *
        omega
      · simpa only [scalarCommand,tripleWords,List.flatMap_cons,List.flatMap,
          List.map_cons, List.flatten_cons, List.cons_append,List.nil_append] using
          hp.seq (.while_true hg₁ (hs.seq hn) hw)
      · rw [hv₃,hv]
        simp [termValue,add_assoc]
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Polynomial source-step bounds for the concrete cached scalar arithmetic.
The stream has three actual binary signed operands per summand, not a stream
of precomputed products or an assumed arithmetic callback. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open scoped BigOperators

theorem scalarCost_poly (n A B : ℕ) :
    scalarCost n A B ≤
      200000000*(n+1)*(A+n*termGrowth B+B+4)^2 := by
  induction n generalizing A with
  | zero =>
    simp only [scalarCost,Nat.zero_mul,Nat.add_zero,Nat.zero_add,Nat.mul_one]
    have h := Nat.pow_le_pow_left (show 4 ≤ A+B+4 by omega) 2
    norm_num at h
    omega
  | succ n ih =>
    let H := A+(n+1)*termGrowth B+B+4
    have htail := ih (A+termGrowth B)
    have hsame : A+termGrowth B+n*termGrowth B+B+4 = H := by dsimp [H]; ring
    rw [hsame] at htail
    have hbase : A+B+4 ≤ H := by dsimp [H]; omega
    have hs := Nat.pow_le_pow_left hbase 2
    have hh : 6*B+11+termCost A B+1 ≤ 200000000*H^2 := by
      dsimp [termCost]
      have hB : B+4 ≤ H := by omega
      have hHpos : 4 ≤ H := by omega
      have hlin : 6*B+12 ≤ 100000000*H^2 := by nlinarith only [hB,hHpos]
      have hmain := Nat.mul_le_mul_left 100000000 hs
      omega
    change 6*B+11+termCost A B+scalarCost n (A+termGrowth B) B+1 ≤
      200000000*(n+1+1)*H^2
    nlinarith only [hh,htail]

def scalarProgram := compiled scalarCommand 0 16

theorem scalarProgram_runsIn (xs : List Triple) (regs : Fin 8 → Bool)
    (acc : WordPair) (A B : ℕ) (ha : pairLength acc ≤ A) (hx : Bounded B xs) :
    ∃ r result,
      RunsIn scalarProgram
        (200000000*(xs.length+1)*(A+xs.length*termGrowth B+B+4)^2+1)
        ((state regs acc ([],[]) ([],[]) (pairEncoding (tripleWords xs))).withPC
          (some scalarProgram.entry))
        ((state r result ([],[]) ([],[]) []).withPC none) ∧
      pairValue result = pairValue acc+(xs.map termValue).sum ∧
      pairLength result ≤ A+xs.length*termGrowth B := by
  obtain ⟨t,ht,r,result,_,he,hv,hl⟩ := scalarCommand_eval xs regs acc A B ha hx
  have hb := scalarCost_poly xs.length A B
  exact ⟨r,result,⟨t+1,by omega,compiled_halt_trace he 0 16⟩,hv,hl⟩

open SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

/-- A signed triple consists of the cached coefficient, the clearing power,
and the cached binomial weight. The arithmetic loop itself multiplies them. -/
def Encodes (A R d h : ℕ) (xs : List Triple) : Prop :=
  xs.length = R-d ∧ ∀ k : Fin xs.length,
    pairValue (xs.get k).1 = coefficientAt A R (d+k.val) ∧
    pairValue (xs.get k).2.1 = (2 : ℤ)^(R-1-(d+k.val)) ∧
    pairValue (xs.get k).2.2 = (h.choose k.val : ℤ)

theorem encodes_sum (A R d h : ℕ) (xs : List Triple) (he : Encodes A R d h xs) :
    (xs.map termValue).sum =
      ∑ k ∈ Finset.range (R-d),
        coefficientAt A R (d+k)*2^(R-1-(d+k))*(h.choose k : ℤ) := by
  have hlist : List.ofFn (fun k : Fin xs.length => termValue (xs.get k)) =
      xs.map termValue := by
    simpa only [List.ofFn_get] using (List.ofFn_comp' xs.get termValue)
  calc
    _ = (List.ofFn (fun k : Fin xs.length => termValue (xs.get k))).sum := by rw [hlist]
    _ = ∑ k : Fin xs.length, termValue (xs.get k) := List.sum_ofFn
    _ = ∑ k : Fin xs.length,
        coefficientAt A R (d+k.val)*2^(R-1-(d+k.val))*(h.choose k.val : ℤ) := by
      apply Finset.sum_congr rfl
      intro k _
      rcases he.2 k with ⟨hc,hp,hb⟩
      simp only [termValue,hc,hp,hb]
    _ = ∑ k ∈ Finset.range xs.length,
        coefficientAt A R (d+k)*2^(R-1-(d+k))*(h.choose k : ℤ) :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ =>
        coefficientAt A R (d+k)*2^(R-1-(d+k))*(h.choose k : ℤ)) xs.length
    _ = _ := by rw [he.1]

/-- Exact arithmetic conclusion for the cached scalar; parity is a separate
swap of the two output words. All three factors are multiplied by the program. -/
theorem scalarProgram_encodes_runsIn (A R d h B : ℕ) (xs : List Triple)
    (regs : Fin 8 → Bool) (he : Encodes A R d h xs) (hb : Bounded B xs) :
    ∃ r result,
      RunsIn scalarProgram
        (200000000*(xs.length+1)*(xs.length*termGrowth B+B+4)^2+1)
        ((state regs ([],[]) ([],[]) ([],[]) (pairEncoding (tripleWords xs))).withPC
          (some scalarProgram.entry))
        ((state r result ([],[]) ([],[]) []).withPC none) ∧
      (-1 : ℤ)^d * pairValue result = scalarSum A R d h ∧
      pairLength result ≤ xs.length*termGrowth B := by
  obtain ⟨r,result,hr,hv,hl⟩ := scalarProgram_runsIn xs regs ([],[]) 0 B (by rfl) hb
  refine ⟨r,result,by simpa using hr,?_,by simpa using hl⟩
  rw [hv]
  have hz : pairValue ([],[]) = 0 := rfl
  rw [hz,zero_add,encodes_sum A R d h xs he]
  rfl

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Exact unsigned component totals for the same concrete scalar program.
The extra invariant controls cancellation without changing any instruction. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def wordTotal (x : WordPair) : ℕ := pairTotal x.1 x.2
@[simp] theorem one_total : wordTotal one = 1 := rfl

def termTotal (x : Triple) : ℕ := wordTotal x.1 * wordTotal x.2.1 * wordTotal x.2.2

theorem multiply_eval_total (regs : Fin 8 → Bool) (acc work next : WordPair)
    (queue : List Bool) :
    ∃ t ≤ 25000*(pairLength work+pairLength next+3)^2+2,
    ∃ r result, Eval multiply t (state regs acc work next queue)
      (state r acc result ([],[]) queue) ∧
      pairValue result = pairValue work * pairValue next ∧
      wordTotal result = wordTotal work * wordTotal next ∧
      pairLength result ≤ 2*(pairLength work+pairLength next)+6 := by
  obtain ⟨t,ht,r,result,he,hv,hm,hl⟩ := streamOperation_eval_total true regs work next queue
  exact ⟨t+1,by omega,r,result,workCall_eval he acc,
    by simpa only [combine,↓reduceIte] using hv,
    by simpa [wordTotal] using hm,
    by simpa only [wordGrowth,↓reduceIte] using hl⟩

theorem accumulate_eval_total (regs : Fin 8 → Bool) (acc work : WordPair)
    (queue : List Bool) :
    ∃ t ≤ 25000*(pairLength acc+pairLength work+3)^2+2,
    ∃ r result, Eval accumulate t (state regs acc work ([],[]) queue)
      (state r result ([],[]) ([],[]) queue) ∧
      pairValue result = pairValue acc + pairValue work ∧
      wordTotal result = wordTotal acc + wordTotal work ∧
      pairLength result ≤ pairLength acc+pairLength work+2 := by
  obtain ⟨t,ht,r,result,he,hv,hm,hl⟩ := streamOperation_eval_total false regs acc work queue
  have hs : embedState id sumPorts (state regs acc work ([],[]) queue)
      (streamData regs acc work queue) = state regs acc work ([],[]) queue := by
    apply embedState_eq_of_ports id sumPorts _ _ _ Function.injective_id sumPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [state,streamData,sumPorts]
    · intro i hi; rfl
  have hf : embedState id sumPorts (state regs acc work ([],[]) queue)
      (streamData r result ([],[]) queue) = state r result ([],[]) ([],[]) queue := by
    apply embedState_eq_of_ports id sumPorts _ _ _ Function.injective_id sumPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [state,streamData,sumPorts]
    · intro i hi
      have h16 : i ≠ 16 := fun h => hi ⟨0, by simpa [sumPorts] using h.symm⟩
      have h17 : i ≠ 17 := fun h => hi ⟨1, by simpa [sumPorts] using h.symm⟩
      have h0 : i ≠ 0 := fun h => hi ⟨2, by simpa [sumPorts] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨3, by simpa [sumPorts] using h.symm⟩
      simp [state,h16,h17,h0,h1]
  have hc := eval_call_lifted (compiled (streamOperation false) 0 1) id sumPorts
    (state regs acc work ([],[]) queue) Function.injective_id sumPorts_injective
    (compiled_halt_trace he 0 1)
  rw [hs,hf] at hc
  exact ⟨t+1,by omega,r,result,hc,
    by simpa only [combine,Bool.false_eq_true,↓reduceIte] using hv,
    by simpa [wordTotal] using hm,
    by simpa only [wordGrowth,Bool.false_eq_true,↓reduceIte] using hl⟩

theorem termStep_eval_total (regs : Fin 8 → Bool) (acc x y z : WordPair)
    (rest : List WordPair) (A B : ℕ)
    (ha : pairLength acc ≤ A) (hx : pairLength x ≤ B)
    (hy : pairLength y ≤ B) (hz : pairLength z ≤ B) :
    ∃ t ≤ termCost A B, ∃ r result,
      Eval termStep t
        (state regs acc ([],[]) x (pairEncoding (y::z::rest)))
        (state r result ([],[]) ([],[]) (pairEncoding rest)) ∧
      pairValue result = pairValue acc + pairValue x*pairValue y*pairValue z ∧
      wordTotal result = wordTotal acc + wordTotal x*wordTotal y*wordTotal z ∧
      pairLength result ≤ A+termGrowth B := by
  have hi := initializeOne_eval regs acc x (pairEncoding (y::z::rest))
  obtain ⟨t₁,ht₁,r₁,w₁,he₁,hv₁,hm₁,hl₁⟩ := multiply_eval_total
    (Function.update regs 0 true) acc one x (pairEncoding (y::z::rest))
  obtain ⟨r₂,_,hp₂⟩ := parse_cons r₁ acc w₁ y (z::rest)
  obtain ⟨t₂,ht₂,r₃,w₂,he₂,hv₂,hm₂,hl₂⟩ := multiply_eval_total r₂ acc w₁ y
    (pairEncoding (z::rest))
  obtain ⟨r₄,_,hp₃⟩ := parse_cons r₃ acc w₂ z rest
  obtain ⟨t₃,ht₃,r₅,w₃,he₃,hv₃,hm₃,hl₃⟩ := multiply_eval_total r₄ acc w₂ z
    (pairEncoding rest)
  obtain ⟨t₄,ht₄,r₆,result,he₄,hv₄,hm₄,hl₄⟩ := accumulate_eval_total r₅ acc w₃
    (pairEncoding rest)
  have hw₁ : pairLength w₁ ≤ 2*B+8 := by simp only [one_length] at hl₁; omega
  have hw₂ : pairLength w₂ ≤ 6*B+22 := by omega
  have hw₃ : pairLength w₃ ≤ 14*B+50 := by omega
  refine ⟨2+(t₁+((6*pairLength y+11)+(t₂+((6*pairLength z+11)+(t₃+t₄))))),
    ?_,r₆,result,hi.seq (he₁.seq (hp₂.seq (he₂.seq (hp₃.seq (he₃.seq he₄))))),?_,?_,?_⟩
  · let H := A+14*B+53
    have h₁ : pairLength one+pairLength x+3 ≤ H := by simp only [one_length]; dsimp [H]; omega
    have h₂ : pairLength w₁+pairLength y+3 ≤ H := by dsimp [H]; omega
    have h₃ : pairLength w₂+pairLength z+3 ≤ H := by dsimp [H]; omega
    have h₄ : pairLength acc+pairLength w₃+3 ≤ H := by dsimp [H]; omega
    have ht₁' := ht₁.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 25000 (Nat.pow_le_pow_left h₁ 2)) 2)
    have ht₂' := ht₂.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 25000 (Nat.pow_le_pow_left h₂ 2)) 2)
    have ht₃' := ht₃.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 25000 (Nat.pow_le_pow_left h₃ 2)) 2)
    have ht₄' := ht₄.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 25000 (Nat.pow_le_pow_left h₄ 2)) 2)
    have hH : H ≤ 14*(A+B+4) := by dsimp [H]; omega
    have hsq := Nat.pow_le_pow_left hH 2
    let M := A+B+4
    have hMB : B+4 ≤ M := by dsimp [M]; omega
    have hMpos : 4 ≤ M := by omega
    have hlin : 12*B+32 ≤ 100*M^2 := by nlinarith only [hMB,hMpos]
    have htime : 2+(t₁+((6*pairLength y+11)+(t₂+
        ((6*pairLength z+11)+(t₃+t₄))))) ≤ 100000*H^2+12*B+32 := by
      omega
    have hsq' : H^2 ≤ 196*M^2 := by
      calc
        H^2 ≤ (14*(A+B+4))^2 := hsq
        _ = 196*M^2 := by dsimp [M]; ring
    change 2+(t₁+((6*pairLength y+11)+(t₂+
      ((6*pairLength z+11)+(t₃+t₄))))) ≤ 100000000*M^2
    omega
  · rw [hv₄,hv₃,hv₂,hv₁,one_value,one_mul]
  · rw [hm₄,hm₃,hm₂,hm₁,one_total,one_mul]
  · dsimp [termGrowth]; omega

theorem scalarCommand_eval_total (xs : List Triple) (regs : Fin 8 → Bool)
    (acc : WordPair) (A B : ℕ) (ha : pairLength acc ≤ A) (hx : Bounded B xs) :
    ∃ t ≤ scalarCost xs.length A B, ∃ r result,
      r 7 = false ∧
      Eval scalarCommand t
        (state regs acc ([],[]) ([],[]) (pairEncoding (tripleWords xs)))
        (state r result ([],[]) ([],[]) []) ∧
      pairValue result = pairValue acc+(xs.map termValue).sum ∧
      wordTotal result = wordTotal acc+(xs.map termTotal).sum ∧
      pairLength result ≤ A+xs.length*termGrowth B := by
  induction xs generalizing regs acc A with
  | nil =>
    obtain ⟨r,hg,he⟩ := parse_nil regs acc ([],[])
    refine ⟨4,le_rfl,r,acc,hg,he.seq (.while_false hg),?_,?_,?_⟩
    · simp
    · simp
    · simpa using ha
  | cons x xs ih =>
    have hb := hx x (by simp)
    have hxs : Bounded B xs := fun y hy => hx y (by simp [hy])
    obtain ⟨r₁,hg₁,hp⟩ := parse_cons regs acc ([],[]) x.1
      (x.2.1::x.2.2::tripleWords xs)
    obtain ⟨ts,hts,r₂,middle,hs,hv,hm,hl⟩ := termStep_eval_total r₁ acc
      x.1 x.2.1 x.2.2 (tripleWords xs) A B ha hb.1 hb.2.1 hb.2.2
    obtain ⟨tt,htt,r₃,result,hg₃,ht,hv₃,hm₃,hl₃⟩ :=
      ih r₂ middle (A+termGrowth B) hl hxs
    cases ht with
    | seq hn hw =>
      rename_i tn tw between
      refine ⟨6*pairLength x.1+11+(ts+tn+tw+1),?_,r₃,result,hg₃,?_,?_,?_,?_⟩
      · simp only [scalarCost,List.length_cons] at *
        omega
      · simpa only [scalarCommand,tripleWords,List.flatMap_cons,List.flatMap,
          List.map_cons, List.flatten_cons, List.cons_append,List.nil_append] using
          hp.seq (.while_true hg₁ (hs.seq hn) hw)
      · rw [hv₃,hv]
        simp [termValue,add_assoc]
      · rw [hm₃,hm]
        simp [termTotal,Nat.add_assoc]
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega

theorem scalarProgram_runsIn_total (xs : List Triple) (regs : Fin 8 → Bool)
    (acc : WordPair) (A B : ℕ) (ha : pairLength acc ≤ A) (hx : Bounded B xs) :
    ∃ r result,
      RunsIn scalarProgram
        (200000000*(xs.length+1)*(A+xs.length*termGrowth B+B+4)^2+1)
        ((state regs acc ([],[]) ([],[]) (pairEncoding (tripleWords xs))).withPC
          (some scalarProgram.entry))
        ((state r result ([],[]) ([],[]) []).withPC none) ∧
      pairValue result = pairValue acc+(xs.map termValue).sum ∧
      wordTotal result = wordTotal acc+(xs.map termTotal).sum ∧
      pairLength result ≤ A+xs.length*termGrowth B := by
  obtain ⟨t,ht,r,result,_,he,hv,hm,hl⟩ := scalarCommand_eval_total xs regs acc A B ha hx
  have hb := scalarCost_poly xs.length A B
  exact ⟨r,result,⟨t+1,by omega,compiled_halt_trace he 0 16⟩,hv,hm,hl⟩

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
