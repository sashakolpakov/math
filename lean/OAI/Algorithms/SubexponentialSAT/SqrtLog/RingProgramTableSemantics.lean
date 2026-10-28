import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableInitial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTablePowers
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCompanionList
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramSerialization
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramCompanion

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

@[simp] theorem listOfFn_get {A : Type*} {d : ℕ} (v : List.Vector A d) :
    List.ofFn v.get = v.val := by
  have h := congrArg List.Vector.toList (List.Vector.ofFn_get v)
  change List.ofFn v.get = v.toList
  simpa only [List.Vector.toList_ofFn] using h

theorem zip_ofFn {A B : Type*} {d : ℕ} (a : Fin d → A) (b : Fin d → B) :
    (List.ofFn a).zip (List.ofFn b) = List.ofFn (fun i => (a i, b i)) := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [List.ofFn_succ, List.zip_cons_cons, ih]

theorem outputWords_correct (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (hminus : wordValue p t minusOne = -1) (pairs : Pairs (baseWidth p t))
    (previous : Word (baseWidth p t)) :
    (outputWords p t M tail minusOne pairs previous).map (wordValue p t) =
      IrreducibleSearch.companionScan (wordValue p t tail) (wordValue p t previous)
        (pairs.map fun x => (wordValue p t x.1, wordValue p t x.2)) := by
  induction pairs generalizing previous with
  | nil => rfl
  | cons pair pairs ih =>
    simp only [outputWords, List.map_cons, IrreducibleSearch.companionScan, ih]
    congr 1
    unfold coefficient RingScan.tripleProduct
    rw [SubexpPreparedQuartic.wordAdd_correct, SubexpPreparedQuartic.wordMul_correct,
      SubexpPreparedQuartic.wordMul_correct, hminus]
    ring

def TailCorrect {B d : ℕ} (v : VectorData B d) : Prop :=
  v.coefficients.val.getLast? = some v.last

theorem outputWords_last (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (hn : pairs ≠ [])
    (previous old : Word (baseWidth p t)) :
    (outputWords p t M tail minusOne pairs previous).getLast? =
      some (lastOutputWord p t M tail minusOne pairs previous old) := by
  induction pairs generalizing previous old with
  | nil => exact False.elim (hn rfl)
  | cons pair pairs ih =>
    cases pairs with
    | nil => rfl
    | cons pair' pairs =>
      simpa only [outputWords, lastOutputWord, List.getLast?_cons_cons] using
        ih (by simp) pair.2 (coefficient p t M tail pair.1 minusOne previous)

theorem advance_tailCorrect (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (zeroWord minusOne : Word (baseWidth p t))
    (c : List.Vector (Word (baseWidth p t)) d) (v : VectorData (baseWidth p t) d) :
    TailCorrect (advance p t M zeroWord minusOne c v) := by
  apply outputWords_last
  intro he
  have h : (c.val.zip v.coefficients.val).length = d := by simp
  rw [he] at h
  simp at h
  omega

theorem tailCorrect_get {B d : ℕ} (hd : 0 < d) (v : VectorData B d)
    (hv : TailCorrect v) :
    v.last = v.coefficients.get ⟨d-1, by omega⟩ := by
  have hne : v.coefficients.val ≠ [] := by
    intro he
    have h := v.coefficients.property
    rw [he] at h
    simp at h
    omega
  have hv' : (List.ofFn v.coefficients.get).getLast? = some v.last := by
    rw [listOfFn_get]
    exact hv
  have hne' : List.ofFn v.coefficients.get ≠ [] := by
    simpa only [listOfFn_get] using hne
  rw [List.getLast?_eq_getLast_of_ne_nil hne', List.getLast_ofFn] at hv'
  exact (Option.some.inj hv').symm

theorem advance_decode (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (zeroWord minusOne : Word (baseWidth p t))
    (hz : wordValue p t zeroWord = 0) (hm : wordValue p t minusOne = -1)
    (c : List.Vector (Word (baseWidth p t)) d) (v : VectorData (baseWidth p t) d)
    (hv : TailCorrect v) :
    (fun i => wordValue p t ((advance p t M zeroWord minusOne c v).coefficients.get i)) =
      IrreducibleSearch.mulX (fun i => wordValue p t (c.get i))
        (fun i => wordValue p t (v.coefficients.get i)) := by
  apply List.ofFn_injective
  change List.ofFn ((wordValue p t) ∘ (advance p t M zeroWord minusOne c v).coefficients.get) = _
  rw [← List.map_ofFn, listOfFn_get]
  change (outputWords p t M v.last minusOne (c.val.zip v.coefficients.val) zeroWord).map _ = _
  rw [outputWords_correct p t M v.last minusOne hm, hz]
  rw [← listOfFn_get c, ← listOfFn_get v.coefficients, zip_ofFn, List.map_ofFn]
  have ht : wordValue p t v.last = IrreducibleSearch.entry
      (fun i => wordValue p t (v.coefficients.get i)) (d-1) := by
    rw [tailCorrect_get hd v hv]
    simp [IrreducibleSearch.entry, show d-1 < d by omega]
  rw [ht]
  exact IrreducibleSearch.companionScan_eq_mulX _ _


theorem literalWords_last {B : ℕ} (n : ℕ) (hn : 0 < n)
    (seed zeroWord old : Word B) :
    (literalWords n seed zeroWord).getLast? = some (literalLastWord n seed zeroWord old) := by
  induction n generalizing seed old with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simpa only [literalWords, literalLastWord, List.getLast?_cons_cons] using
        ih (by omega) zeroWord seed

theorem initialData_tailCorrect {B d : ℕ} (hd : 0 < d) (oneWord zeroWord : Word B) :
    TailCorrect (initialData d oneWord zeroWord) :=
  literalWords_last d hd oneWord zeroWord zeroWord

theorem literalWords_ofFn {B : ℕ} (n : ℕ) (oneWord zeroWord : Word B) :
    literalWords n oneWord zeroWord =
      List.ofFn (fun i : Fin n => if i.val = 0 then oneWord else zeroWord) := by
  induction n generalizing oneWord with
  | zero => rfl
  | succ n ih =>
    simp [literalWords, List.ofFn_succ, ih ]

theorem initialData_get {B d : ℕ} (oneWord zeroWord : Word B) (i : Fin d) :
    (initialData d oneWord zeroWord).coefficients.get i =
      if i.val = 0 then oneWord else zeroWord := by
  have hv : (initialData d oneWord zeroWord).coefficients =
      List.Vector.ofFn (fun i : Fin d => if i.val = 0 then oneWord else zeroWord) := by
    apply Subtype.ext
    change literalWords d oneWord zeroWord =
      (List.Vector.ofFn (fun i : Fin d => if i.val = 0 then oneWord else zeroWord)).toList
    rw [List.Vector.toList_ofFn]
    exact literalWords_ofFn d oneWord zeroWord
  rw [hv]
  exact List.Vector.get_ofFn _ _

theorem initialData_decode (p t : ℕ) [Fact p.Prime] {d : ℕ}
    (oneWord zeroWord : Word (baseWidth p t))
    (ho : wordValue p t oneWord = 1) (hz : wordValue p t zeroWord = 0) :
    (fun i => wordValue p t ((initialData d oneWord zeroWord).coefficients.get i)) =
      IrreducibleSearch.oneVector d := by
  funext i
  rw [initialData_get]
  simp only [IrreducibleSearch.oneVector]
  split <;> simp_all


theorem iterData_succ (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ}
    (zeroWord minusOne : Word (baseWidth p t)) (c : List.Vector (Word (baseWidth p t)) d)
    (n : ℕ) (v : VectorData (baseWidth p t) d) :
    iterData p t M zeroWord minusOne c (n+1) v =
      advance p t M zeroWord minusOne c (iterData p t M zeroWord minusOne c n v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => exact ih (advance p t M zeroWord minusOne c v)

theorem iterData_tailCorrect (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (zeroWord minusOne : Word (baseWidth p t)) (c : List.Vector (Word (baseWidth p t)) d)
    (n : ℕ) (v : VectorData (baseWidth p t) d) (hv : TailCorrect v) :
    TailCorrect (iterData p t M zeroWord minusOne c n v) := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [iterData_succ]
    exact advance_tailCorrect p t M hd zeroWord minusOne c _

theorem powerData_decode (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (oneWord zeroWord minusOne : Word (baseWidth p t))
    (ho : wordValue p t oneWord = 1) (hz : wordValue p t zeroWord = 0)
    (hm : wordValue p t minusOne = -1) (c : List.Vector (Word (baseWidth p t)) d) (n : ℕ) :
    (fun i => wordValue p t ((iterData p t M zeroWord minusOne c n
      (initialData d oneWord zeroWord)).coefficients.get i)) =
      IrreducibleSearch.powerVector (fun i => wordValue p t (c.get i)) n := by
  induction n with
  | zero =>
    simpa only [iterData, IrreducibleSearch.powerVector, IrreducibleSearch.cacheVector_eq] using
      initialData_decode p t oneWord zeroWord ho hz
  | succ n ih =>
    rw [iterData_succ, advance_decode p t M hd zeroWord minusOne hz hm c _
      (iterData_tailCorrect p t M hd zeroWord minusOne c n _
        (initialData_tailCorrect hd oneWord zeroWord)), ih]
    simp only [IrreducibleSearch.powerVector, IrreducibleSearch.cacheVector_eq]

open SubexponentialSAT.BinaryArithmetic in
theorem outputWords_canonical (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (previous : Word (baseWidth p t)) :
    ∀ x ∈ outputWords p t M tail minusOne pairs previous, BinaryArithmetic.toNat x.val < p^t := by
  induction pairs generalizing previous with
  | nil => simp [outputWords]
  | cons pair pairs ih =>
    intro x hx
    rcases List.mem_cons.mp hx with heq | hx
    · subst x
      exact SubexpPreparedQuartic.wordAdd_canonical p t M _ _
    · exact ih pair.2 x hx

open SubexponentialSAT.BinaryArithmetic in
theorem advance_canonical (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ}
    (zeroWord minusOne : Word (baseWidth p t)) (c : List.Vector (Word (baseWidth p t)) d)
    (v : VectorData (baseWidth p t) d) (i : Fin d) :
    BinaryArithmetic.toNat ((advance p t M zeroWord minusOne c v).coefficients.get i).val < p^t := by
  have hm : (advance p t M zeroWord minusOne c v).coefficients.get i ∈
      (advance p t M zeroWord minusOne c v).coefficients.val := by
    rw [← listOfFn_get]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  exact outputWords_canonical p t M v.last minusOne _ zeroWord _ hm

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
