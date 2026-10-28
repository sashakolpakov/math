import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrenceFormula
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalarTotal
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramMagnitude
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramTotal

namespace OAI.Algorithms

-- LayoutTriplePreparationProgramAlgebra.lean

/-! The factored triple stream uses the positive H cache directly. The outer
parity and both powers in a scalar summand are combined before serialization. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open scoped BigOperators
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm
open SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

def factoredTerm (A R d h k : ℕ) : ℤ :=
  ((-1 : ℤ)^(A+k) * (H A (R-1-d-k) : ℤ)) * 2^(R-1) * (h.choose k : ℤ)

theorem coefficientAt_H (A R j : ℕ) (hj : j < R) :
    LayoutCoefficientAlgorithm.coefficientAt A R j =
      (-1 : ℤ)^(A+j)*2^j*(H A (R-1-j) : ℤ) := by
  rw [LayoutCoefficientAlgorithm.coefficientAt_eq]
  simpa [SubexponentialSAT.BinomialInterpolation.extendCoefficients,hj] using parity_eq_H A R ⟨j,hj⟩

theorem factoredTerm_eq (A R d h k : ℕ) (hk : k < R-d) :
    factoredTerm A R d h k = (-1 : ℤ)^d *
      (LayoutCoefficientAlgorithm.coefficientAt A R (d+k) *
        2^(R-1-(d+k)) * (h.choose k : ℤ)) := by
  have hj : d+k < R := by omega
  have he : d+k+(R-1-(d+k)) = R-1 := by omega
  have hm : R-1-d-k = R-1-(d+k) := by omega
  have hs : (-1 : ℤ)^d * (-1)^(A+(d+k)) = (-1)^(A+k) := by
    rw [← pow_add, show d+(A+(d+k)) = (A+k)+2*d by omega,
      pow_add, pow_mul]
    norm_num
  have hp : (2 : ℤ)^(R-1) = 2^(d+k)*2^(R-1-(d+k)) := by rw [← pow_add,he]
  rw [coefficientAt_H A R (d+k) hj]
  unfold factoredTerm
  rw [hm]
  calc
    _ = ((-1 : ℤ)^d * (-1)^(A+(d+k))) *
        (H A (R-1-(d+k)) : ℤ) * (2^(d+k)*2^(R-1-(d+k))) * (h.choose k : ℤ) := by
      rw [hp,hs]
    _ = _ := by ring

def FactoredEncodes (A R d h : ℕ) (xs : List Triple) : Prop :=
  xs.length = R-d ∧ ∀ k : Fin xs.length,
    pairValue (xs.get k).1 = (-1 : ℤ)^(A+k.val)*(H A (R-1-d-k.val) : ℤ) ∧
    pairValue (xs.get k).2.1 = (2 : ℤ)^(R-1) ∧
    pairValue (xs.get k).2.2 = (h.choose k.val : ℤ)

theorem factoredEncodes_sum (A R d h : ℕ) (xs : List Triple)
    (he : FactoredEncodes A R d h xs) :
    (xs.map termValue).sum = scalarSum A R d h := by
  have hl : List.ofFn (fun k : Fin xs.length => termValue (xs.get k)) =
      xs.map termValue := by
    simpa only [List.ofFn_get,Function.comp_def] using
      (List.map_ofFn (f := xs.get) (g := termValue)).symm
  calc
    _ = (List.ofFn (fun k : Fin xs.length => termValue (xs.get k))).sum := by rw [hl]
    _ = ∑ k : Fin xs.length, termValue (xs.get k) := List.sum_ofFn
    _ = ∑ k : Fin xs.length, factoredTerm A R d h k.val := by
      apply Finset.sum_congr rfl
      intro k _
      rcases he.2 k with ⟨hc,hp,hb⟩
      simp only [termValue,hc,hp,hb,factoredTerm]
    _ = ∑ k ∈ Finset.range xs.length, factoredTerm A R d h k :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ => factoredTerm A R d h k) xs.length
    _ = ∑ k ∈ Finset.range (R-d), (-1 : ℤ)^d *
        (LayoutCoefficientAlgorithm.coefficientAt A R (d+k)*
          2^(R-1-(d+k))*(h.choose k : ℤ)) := by
      rw [he.1]
      apply Finset.sum_congr rfl
      intro k hk
      exact factoredTerm_eq A R d h k (Finset.mem_range.mp hk)
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- The unmodified scalar machine now returns the numerator itself. -/
theorem factored_scalarProgram_runsIn (A R d h B : ℕ) (xs : List Triple)
    (regs : Fin 8 → Bool) (he : FactoredEncodes A R d h xs) (hb : Bounded B xs) :
    ∃ r result,
      SubexponentialSAT.BitProgram.RunsIn scalarProgram
        (200000000*(xs.length+1)*(xs.length*termGrowth B+B+4)^2+1)
        ((LayoutProgramScalar.state regs ([],[]) ([],[]) ([],[])
          (pairEncoding (tripleWords xs))).withPC (some scalarProgram.entry))
        ((LayoutProgramScalar.state r result ([],[]) ([],[]) []).withPC none) ∧
      pairValue result = scalarSum A R d h ∧
      pairLength result ≤ xs.length*termGrowth B := by
  obtain ⟨r,result,hr,hv,hl⟩ := scalarProgram_runsIn xs regs ([],[]) 0 B (by rfl) hb
  refine ⟨r,result,by simpa [tripleWords, LayoutProgramScalar.tripleWords] using hr,
    ?_,by simpa using hl⟩
  rw [hv,show pairValue ([],[]) = 0 from rfl,zero_add,factoredEncodes_sum A R d h xs he]

theorem factoredMass_eq (A R d h k : ℕ) (hk : k < R-d) :
    H A (R-1-d-k)*2^(R-1)*h.choose k =
      (LayoutCoefficientAlgorithm.coefficientAt A R (d+k)).natAbs *
        2^(R-1-(d+k))*h.choose k := by
  rw [coefficientAt_H A R (d+k) (by omega)]
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_neg,Int.natAbs_one,
    one_pow,Int.natAbs_natCast,one_mul]
  have he : d+k+(R-1-(d+k)) = R-1 := by omega
  have hm : R-1-d-k = R-1-(d+k) := by omega
  have hp : (2 : ℕ)^(R-1) = 2^(d+k)*2^(R-1-(d+k)) := by rw [← pow_add,he]
  rw [hm,hp]
  ring

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramSemantics.lean

/-! The actual generated stream has the exact coefficient sum and nonnegative
mass required by the scalar machine, despite the factored cache representation. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open scoped BigOperators
open RowSelectionProgram LayoutProgramScalar LayoutCoefficientRecurrence
open SubexponentialSAT.Subexp.MatrixParityProgram (toggle sign)

theorem signedPair_value (s : Bool) (p n : List Bool) :
    pairValue (signedPair s p n) = sign s * pairValue (p,n) := by
  cases s <;> simp [signedPair,pairValue,sign,RowSelectionProgram.signedValue]

theorem signedPair_total (s : Bool) (p n : List Bool) :
    wordTotal (signedPair s p n) = wordTotal (p,n) := by
  cases s <;> simp [signedPair,wordTotal,pairTotal,Nat.add_comm]

theorem preparedTriples_eq_ofFn (c : Cache) (s : Bool) (n k : ℕ) :
    preparedTriples c s n k = List.ofFn (fun i : Fin n =>
      triple c (toggle i.val s) (n-1-i.val) (k+i.val)) := by
  induction n generalizing s k with
  | zero => rfl
  | succ n ih =>
    rw [preparedTriples,List.ofFn_succ]
    congr 1
    rw [ih]
    apply congrArg List.ofFn
    funext i
    simp only [Fin.val_succ,toggle]
    congr 1 <;> omega

theorem preparedTriples_get (c : Cache) (s : Bool) (n k i : ℕ) (hi : i < n) :
    (preparedTriples c s n k)[i]'(by simpa using hi) =
      triple c (toggle i s) (n-1-i) (k+i) := by
  simp [preparedTriples_eq_ofFn]

def Cache.Values (c : Cache) (A R h : ℕ) : Prop :=
  (∀ i < R, pairValue (c.Hword i) = (H A i : ℤ)) ∧
  pairValue c.power = (2 : ℤ)^(R-1) ∧
  (∀ k < R, pairValue (c.Bword k) = (h.choose k : ℤ))

def Cache.Totals (c : Cache) (A R h : ℕ) : Prop :=
  (∀ i < R, wordTotal (c.Hword i) = H A i) ∧
  wordTotal c.power = 2^(R-1) ∧
  (∀ k < R, wordTotal (c.Bword k) = h.choose k)

theorem prepared_factoredEncodes (c : Cache) (A R d h : ℕ)
    (hv : c.Values A R h) :
    FactoredEncodes A R d h (preparedTriples c (toggle A false) (R-d) 0) := by
  refine ⟨preparedTriples_length c _ _ _,?_⟩
  intro k
  have hk : k.val < R-d := by simpa using k.isLt
  have hi : R-d-1-k.val < R := by omega
  have hkR : k.val < R := by omega
  have hget := preparedTriples_get c (toggle A false) (R-d) 0 k.val hk
  simp only [List.get_eq_getElem] at ⊢
  rw [hget]
  have hsign : sign (K := ℤ) (toggle k.val (toggle A false)) = (-1 : ℤ)^(A+k.val) := by
    rw [SubexponentialSAT.Subexp.MatrixParityProgram.sign_toggle,
      SubexponentialSAT.Subexp.MatrixParityProgram.false_sign_toggle,pow_add,mul_comm]
  have hindex : R-d-1-k.val = R-1-d-k.val := by omega
  change pairValue (signedPair (toggle k.val (toggle A false))
      (c.Hword (R-d-1-k.val)).1 (c.Hword (R-d-1-k.val)).2) = _ ∧
    pairValue c.power = _ ∧ pairValue (c.Bword (0+k.val)) = _
  rw [signedPair_value,hsign,hv.1 _ hi,hindex]
  exact ⟨rfl,hv.2.1,by simpa using hv.2.2 _ hkR⟩

theorem prepared_bounded (c : Cache) (s : Bool) (n k B : ℕ)
    (hu : c.Uniform) (hf : c.Fits (n+k))
    (hW : 2*c.width.length ≤ B) (hP : pairLength c.power ≤ B) :
    Bounded B (preparedTriples c s n k) := by
  induction n generalizing s k with
  | zero => simp [Bounded,preparedTriples]
  | succ n ih =>
    have hh := c.Hword_length hu n (by have := hf.1; omega) (by have := hf.2.1; omega)
    have hb := c.Bword_length hu k (by have := hf.2.2.1; omega) (by have := hf.2.2.2; omega)
    have hf' : c.Fits (n+(k+1)) := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hf
    intro t ht
    simp only [preparedTriples,List.mem_cons] at ht
    rcases ht with rfl | ht
    · change pairLength (signedPair s (c.Hword n).1 (c.Hword n).2) ≤ B ∧
        pairLength c.power ≤ B ∧ pairLength (c.Bword k) ≤ B
      rw [signedPair_length]
      exact ⟨by change pairLength (c.Hword n) ≤ B; omega,hP,by omega⟩
    · exact ih (!s) (k+1) hf' t ht

def FactoredTotalEncodes (A R d h : ℕ) (xs : List LayoutProgramScalar.Triple) : Prop :=
  xs.length = R-d ∧ ∀ k : Fin xs.length,
    termTotal (xs.get k) = H A (R-1-d-k.val)*2^(R-1)*h.choose k.val

theorem prepared_totalEncodes (c : Cache) (A R d h : ℕ)
    (hv : c.Totals A R h) (s : Bool) :
    FactoredTotalEncodes A R d h (preparedTriples c s (R-d) 0) := by
  refine ⟨preparedTriples_length c _ _ _,?_⟩
  intro k
  have hk : k.val < R-d := by simpa using k.isLt
  have hi : R-d-1-k.val < R := by omega
  have hkR : k.val < R := by omega
  have hget := preparedTriples_get c s (R-d) 0 k.val hk
  simp only [List.get_eq_getElem] at ⊢
  rw [hget]
  simp only [termTotal,triple,signedPair_total,Nat.zero_add]
  rw [hv.1 _ hi,hv.2.1,hv.2.2 _ hkR]
  have hindex : R-d-1-k.val = R-1-d-k.val := by omega
  rw [hindex]

theorem factoredTotalEncodes_sum (A R d h : ℕ) (xs : List LayoutProgramScalar.Triple)
    (he : FactoredTotalEncodes A R d h xs) :
    (xs.map termTotal).sum = LayoutProgram.scalarMass R d h
      (fun j => (LayoutCoefficientAlgorithm.coefficientAt A R j).natAbs) := by
  have hl : List.ofFn (fun k : Fin xs.length => termTotal (xs.get k)) =
      xs.map termTotal := by
    simpa only [List.ofFn_get,Function.comp_def] using
      (List.map_ofFn (f := xs.get) (g := termTotal)).symm
  calc
    _ = (List.ofFn (fun k : Fin xs.length => termTotal (xs.get k))).sum := by rw [hl]
    _ = ∑ k : Fin xs.length, termTotal (xs.get k) := List.sum_ofFn
    _ = ∑ k : Fin xs.length, H A (R-1-d-k.val)*2^(R-1)*h.choose k.val := by
      apply Finset.sum_congr rfl
      intro k _
      exact he.2 k
    _ = ∑ k ∈ Finset.range xs.length, H A (R-1-d-k)*2^(R-1)*h.choose k :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ => H A (R-1-d-k)*2^(R-1)*h.choose k) xs.length
    _ = _ := by
      rw [he.1]
      apply Finset.sum_congr rfl
      intro k hk
      exact factoredMass_eq A R d h k (Finset.mem_range.mp hk)

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramInterface.lean

/-! One consumer-facing contract for native triple preparation. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

/-- The produced stream is already in the scalar machine's exact triple order.
Its signed sum is the numerator and its total is the no-cancellation budget. -/
theorem prepareProgram_factored_runsIn (c : Cache) (regs : Fin 9 → Bool)
    (counter parity : List Bool) (A R d h : ℕ)
    (hc : counter.length = R-d) (ha : parity.length = A)
    (hu : c.Uniform) (hf : c.Fits (R-d))
    (hv : c.Values A R h) (hm : c.Totals A R h) :
    ∃ r xs,
      RunsIn prepareProgram
        (9*(R-d)+3*A+(R-d)*((R-d)*(28*c.width.length+34)+140*c.width.length+
          18*pairLength c.power+222)+3*((R-d)*(8*c.width.length+2*pairLength c.power+9))+24)
        ((cacheState c regs counter [] [] [] [] parity).withPC (some prepareProgram.entry))
        ((cacheState c r [] [] [] []
          (pairEncoding (LayoutProgramScalar.tripleWords xs)) []).withPC none) ∧
      FactoredEncodes A R d h xs ∧ FactoredTotalEncodes A R d h xs ∧
      LayoutProgramScalar.Bounded (2*c.width.length+pairLength c.power) xs ∧
      (xs.map LayoutProgramScalar.termValue).sum = LayoutCoefficientAlgorithm.scalarSum A R d h ∧
      (xs.map LayoutProgramScalar.termTotal).sum = LayoutProgram.scalarMass R d h
        (fun j => (LayoutCoefficientAlgorithm.coefficientAt A R j).natAbs) := by
  let xs := preparedTriples c (SubexponentialSAT.Subexp.MatrixParityProgram.toggle A false) (R-d) 0
  obtain ⟨r,he⟩ := prepareProgram_runsIn c regs counter parity hu (by simpa [hc] using hf)
  have hx : FactoredEncodes A R d h xs := prepared_factoredEncodes c A R d h hv
  have ht : FactoredTotalEncodes A R d h xs := prepared_totalEncodes c A R d h hm _
  refine ⟨r,xs,by simpa [hc,ha,xs,tripleWords,LayoutProgramScalar.tripleWords] using he,hx,ht,?_,
    factoredEncodes_sum A R d h xs hx,factoredTotalEncodes_sum A R d h xs ht⟩
  exact prepared_bounded c _ (R-d) 0 _ hu (by simpa using hf) (by omega) (by omega)

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open RowSelectionProgram LayoutProgramScalar LayoutCoefficientRecurrence
open SubexponentialSAT.BinaryArithmetic

/-- Cache representation supplied by the native unsigned cache builders. -/
def unsignedCache (Hwords Bwords : List (List Bool)) (width : List Bool)
    (power : WordPair) (R : ℕ) : Cache :=
  ⟨Hwords,List.replicate R (List.replicate width.length false),
    Bwords,List.replicate R (List.replicate width.length false),width,power⟩

theorem zeroWord_value (W : ℕ) : BinaryArithmetic.toNat (List.replicate W false) = 0 := by
  induction W with
  | zero => rfl
  | succ W ih => simp [List.replicate_succ,ih]

theorem zeroRows_flatten (R W : ℕ) :
    (List.replicate R (List.replicate W false)).flatten = List.replicate (R*W) false := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [List.replicate_succ,List.flatten_cons,ih,← List.replicate_add]
    congr 1
    ring

theorem decoded_getD (words : List (List Bool)) (f : ℕ → ℕ) (R i : ℕ)
    (hlen : words.length = R) (hv : words.map BinaryArithmetic.toNat = (List.range R).map f)
    (hi : i < R) : BinaryArithmetic.toNat (words.getD i []) = f i := by
  have hiw : i < words.length := by omega
  have him : i < (words.map BinaryArithmetic.toNat).length := by simpa using hiw
  have hir : i < ((List.range R).map f).length := by simpa using hi
  have hh := congrArg (fun xs : List ℕ => xs.getD i 0) hv
  rw [List.getD_eq_getElem _ _ him,List.getD_eq_getElem _ _ hir] at hh
  simp only [List.getElem_map,List.getElem_range] at hh
  rw [List.getD_eq_getElem _ _ hiw]
  exact hh

theorem unsignedRow_entry (words : List (List Bool)) (f : ℕ → ℕ) (R W i : ℕ)
    (hlen : words.length = R) (hv : words.map BinaryArithmetic.toNat = (List.range R).map f)
    (hi : i < R) :
    pairValue (words.getD i [],(List.replicate R (List.replicate W false)).getD i []) =
      (f i : ℤ) ∧
    wordTotal (words.getD i [],(List.replicate R (List.replicate W false)).getD i []) = f i := by
  have hh := decoded_getD words f R i hlen hv hi
  have hz : (List.replicate R (List.replicate W false)).getD i [] =
      List.replicate W false := List.getD_replicate (List.replicate W false) hi
  change ((BinaryArithmetic.toNat (words.getD i []) : ℤ) -
      (BinaryArithmetic.toNat ((List.replicate R (List.replicate W false)).getD i []) : ℤ) = (f i : ℤ)) ∧
    BinaryArithmetic.toNat (words.getD i []) + BinaryArithmetic.toNat ((List.replicate R (List.replicate W false)).getD i []) = f i
  rw [hz,zeroWord_value,hh]
  simp

/-- All representation hypotheses needed by the native preparation theorem
follow from the native H/Pascal builders' unsigned rows and the power word. -/
theorem unsignedCache_contract (Hwords Bwords : List (List Bool)) (width : List Bool)
    (power : WordPair) (A R d h : ℕ)
    (hlen : Hwords.length = R) (blen : Bwords.length = R)
    (hw : ∀ w ∈ Hwords, w.length = width.length)
    (bw : ∀ w ∈ Bwords, w.length = width.length)
    (hv : Hwords.map BinaryArithmetic.toNat = (List.range R).map (H A))
    (bv : Bwords.map BinaryArithmetic.toNat = (List.range R).map (h.choose))
    (pv : pairValue power = (2 : ℤ)^(R-1))
    (pt : wordTotal power = 2^(R-1)) :
    let c := unsignedCache Hwords Bwords width power R
    c.Uniform ∧ c.Fits (R-d) ∧ c.Values A R h ∧ c.Totals A R h := by
  let c := unsignedCache Hwords Bwords width power R
  have hz : ∀ w ∈ List.replicate R (List.replicate width.length false), w.length = width.length := by
    intro w hw
    rcases List.mem_replicate.mp hw with ⟨_,rfl⟩
    simp
  have hhe (i : ℕ) (hi : i < R) := unsignedRow_entry Hwords (H A) R width.length i hlen hv hi
  have hbe (i : ℕ) (hi : i < R) := unsignedRow_entry Bwords (h.choose) R width.length i blen bv hi
  refine ⟨⟨hw,hz,bw,hz⟩,?_,⟨?_,pv,?_⟩,⟨?_,pt,?_⟩⟩
  · simp [Cache.Fits,unsignedCache,hlen,blen]
  · intro i hi
    exact (hhe i hi).1
  · intro i hi
    exact (hbe i hi).1
  · intro i hi
    exact (hhe i hi).2
  · intro i hi
    exact (hbe i hi).2

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
