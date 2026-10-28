import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramDictionaryInsert
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanBridge

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

def codePairs {B d : ℕ} (x y : RingProgram.Code (Word B) d) : List (Word B × Word B) :=
  List.ofFn fun i => (x i,y i)

theorem leftBits_codePairs {B d : ℕ} (x y : RingProgram.Code (Word B) d) :
    RingScan.leftBits (codePairs x y) = RingProgram.flat x := by
  have h (l : List (Word B × Word B)) : RingScan.leftBits l = (l.map fun z => z.1.val).flatten := by
    induction l with
    | nil => rfl
    | cons z l ih => simp only [RingScan.leftBits,List.map_cons,List.flatten_cons,ih]
  simp only [h,codePairs,List.map_ofFn,RingProgram.flat,Function.comp_def]

theorem rightBits_codePairs {B d : ℕ} (x y : RingProgram.Code (Word B) d) :
    RingScan.rightBits (codePairs x y) = RingProgram.flat y := by
  have h (l : List (Word B × Word B)) : RingScan.rightBits l = (l.map fun z => z.2.val).flatten := by
    induction l with
    | nil => rfl
    | cons z l ih => simp only [RingScan.rightBits,List.map_cons,List.flatten_cons,ih]
  simp only [h,codePairs,List.map_ofFn,RingProgram.flat,Function.comp_def]

theorem sumBits_codePairs (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (x y : RingProgram.Code (Word (baseWidth p t)) d) :
    RingScan.sumBits p t M (codePairs x y) =
      RingProgram.flat (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1 := by
  have h (l : List (Word (baseWidth p t) × Word (baseWidth p t))) :
      RingScan.sumBits p t M l = (l.map fun z => (SubexpPreparedQuartic.wordAdd p t M z.1 z.2).1.val).flatten := by
    induction l with
    | nil => rfl
    | cons z l ih => simp only [RingScan.sumBits,List.map_cons,List.flatten_cons,ih]
  simp only [h,codePairs,List.map_ofFn,RingProgram.flat,RingProgram.addRun,
    RingProgram.tabulateRun_eq,RingProgram.scalarProgram,Function.comp_def]

theorem lookup_encode (key : K → List Bool) {C : Type*} (coeff : C → List Bool)
    (hk : Function.Injective key) (entries : List (K × C)) (k : K) :
    (Squarefree.Program.encodeDictionary key coeff entries).lookup (key k) =
      (entries.lookup k).map coeff := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨j,c⟩
    by_cases h : j=k
    · subst j; simp [Squarefree.Program.encodeDictionary]
    · have he : key j ≠ key k := fun hh => h (hk hh)
      simp only [Squarefree.Program.encodeDictionary,List.map_cons,List.lookup_cons] at ih ⊢
      simp [beq_false_of_ne (Ne.symm h),beq_false_of_ne (Ne.symm he),ih]

/-- Concrete coefficient-code update. Coefficients are fixed-width words;
the actual native addition above refines this finite operation exactly. -/
def insertCode (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d)) :=
  let value := match entries.lookup k with
    | none => x
    | some y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1
  (k,value) :: (Squarefree.Sparse.erase k entries).reverse

def codeBranchBudget (B d : ℕ) : ℕ := d * (6000 * (B+1)^2 + 50*B + 36) + 23

theorem hitBudget_codePairs (p t : ℕ) {d : ℕ}
    (x y : RingProgram.Code (Word (baseWidth p t)) d) :
    hitBudget p t (codePairs x y) = codeBranchBudget (baseWidth p t) d := by
  rw [hitBudget,leftBits_codePairs,rightBits_codePairs]
  simp only [RingProgram.flat_length,codePairs,List.length_ofFn,codeBranchBudget]
  ring


theorem encoded_update {C : Type*} (key : K → List Bool) (coeff : C → List Bool)
    (hk : Function.Injective key) (entries : List (K × C)) (k : K) (c : C) :
    Squarefree.Program.rawEntries (Squarefree.Program.encodeDictionary key coeff
      ((k,c)::(Squarefree.Sparse.erase k entries).reverse)) =
    updatedBytes (Squarefree.Program.encodeDictionary key coeff entries) (key k) (coeff c) := by
  simp only [Squarefree.Program.encodeDictionary,List.map_cons,List.map_reverse,updatedBytes]
  have he : List.map (fun a : K × C => (key a.1,coeff a.2)) (Squarefree.Sparse.erase k entries) =
      Squarefree.Program.erasedEntries (key k) (List.map (fun a : K × C => (key a.1,coeff a.2)) entries) := by
    induction entries with
    | nil => rfl
    | cons a entries ih =>
      by_cases h : a.1 = k
      · simp [Squarefree.Sparse.erase,Squarefree.Program.erasedEntries,h] at ih ⊢
        exact ih
      · have h' : key a.1 ≠ key k := fun e => h (hk e)
        simp [Squarefree.Sparse.erase,Squarefree.Program.erasedEntries,h,h'] at ih ⊢
        exact ih
  rw [he]

/-- The real insertion machine refines normalized additive insertion on concrete
coefficient vectors. It executes the same fixed table for every dimension. -/
theorem insert_code_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (key : K → List Bool) (hk : Function.Injective key)
    (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (regs : Fin 8 → Bool) (width count : List Bool)
    (hc : count.length = d) (hw : width.length = baseWidth p t) :
    let encoded := Squarefree.Program.encodeDictionary key RingProgram.flat entries
    let value := match entries.lookup k with
      | none => x
      | some y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1
    ∃ n ≤ insertBudget encoded (key k) (RingProgram.flat value) (codeBranchBudget (baseWidth p t) d),
    ∃ rr, Eval insert n (machine regs (inputTape M.bits width count encoded (key k) (RingProgram.flat x)))
      (machine rr (outputTape M.bits width count
        (Squarefree.Program.rawEntries (Squarefree.Program.encodeDictionary key RingProgram.flat
          (insertCode p t M cache k x entries))) (RingProgram.flat x))) := by
  dsimp only
  cases he : entries.lookup k with
  | none =>
    have hl : (Squarefree.Program.encodeDictionary key RingProgram.flat entries).lookup (key k) = none := by
      rw [lookup_encode key RingProgram.flat hk,he]; rfl
    obtain ⟨n,hn,rr,hr⟩ := insert_miss_eval regs M.bits width count
      (Squarefree.Program.encodeDictionary key RingProgram.flat entries) (key k) (RingProgram.flat x) hl
    refine ⟨n,?_,rr,?_⟩
    · have hb : 7 * (RingProgram.flat x).length + 5 ≤ codeBranchBudget (baseWidth p t) d := by
        rw [RingProgram.flat_length]
        dsimp [codeBranchBudget]
        nlinarith [Nat.zero_le (d*(6000*(baseWidth p t+1)^2))]
      simp only [] at ⊢
      dsimp [insertBudget] at hn ⊢
      omega
    · simpa only [insertCode,he,encoded_update key RingProgram.flat hk] using hr
  | some y =>
    have hl : (Squarefree.Program.encodeDictionary key RingProgram.flat entries).lookup (key k) =
        some (RingScan.rightBits (codePairs x y)) := by
      rw [lookup_encode key RingProgram.flat hk,he,rightBits_codePairs]; rfl
    obtain ⟨n,hn,rr,hr⟩ := insert_hit_eval p t M (codePairs x y) regs width count
      (Squarefree.Program.encodeDictionary key RingProgram.flat entries) (key k) hl
      (by simpa only [codePairs,List.length_ofFn] using hc) hw
    refine ⟨n,?_,rr,?_⟩
    · simpa only [he,hitBudget_codePairs,sumBits_codePairs p t M cache] using hn
    · simpa only [insertCode,he,encoded_update key RingProgram.flat hk,
        leftBits_codePairs,sumBits_codePairs p t M cache] using hr

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
