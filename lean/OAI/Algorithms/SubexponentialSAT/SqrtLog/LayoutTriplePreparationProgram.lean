import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgramBasic
import OAI.Algorithms.SubexponentialSAT.Subexp.GatherProgram

namespace OAI.Algorithms


-- LayoutTriplePreparationProgramLookup.lean

/-! List-level cache representation for the preserving physical array scan. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- All five cache inputs are preserved throughout preparation. -/
structure Cache where
  Hpositive : List (List Bool)
  Hnegative : List (List Bool)
  Bpositive : List (List Bool)
  Bnegative : List (List Bool)
  width : List Bool
  power : RowSelectionProgram.WordPair

/-- The words stored in the cache, before selecting their sign. -/
def Cache.Hword (c : Cache) (i : ℕ) : RowSelectionProgram.WordPair :=
  (c.Hpositive.getD i [],c.Hnegative.getD i [])
def Cache.Bword (c : Cache) (i : ℕ) : RowSelectionProgram.WordPair :=
  (c.Bpositive.getD i [],c.Bnegative.getD i [])

def Cache.Uniform (c : Cache) : Prop :=
  (∀ w ∈ c.Hpositive, w.length = c.width.length) ∧
  (∀ w ∈ c.Hnegative, w.length = c.width.length) ∧
  (∀ w ∈ c.Bpositive, w.length = c.width.length) ∧
  (∀ w ∈ c.Bnegative, w.length = c.width.length)

def Cache.Fits (c : Cache) (N : ℕ) : Prop :=
  N ≤ c.Hpositive.length ∧ N ≤ c.Hnegative.length ∧
  N ≤ c.Bpositive.length ∧ N ≤ c.Bnegative.length

def cacheState (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool)
    (work : RowSelectionProgram.WordPair := ([],[])) : Data :=
  ⟨regs,![c.Hpositive.flatten,c.Hnegative.flatten,c.Bpositive.flatten,c.Bnegative.flatten,
    c.width,c.power.1,c.power.2,counter,hindex,kindex,[],work.1,work.2,[],[],[],[],
    buffer,queue,parity]⟩

theorem readCached_get (binomial : Bool) (d : Data)
    (ps ns : List (List Bool)) (i : ℕ)
    (hp : d.stacks (readPorts binomial 0) = ps.flatten)
    (hn : d.stacks (readPorts binomial 1) = ns.flatten)
    (hi : (d.stacks (readPorts binomial 2)).length = i)
    (hip : i < ps.length) (hin : i < ns.length)
    (hwp : ∀ w ∈ ps, w.length = (d.stacks 4).length)
    (hwn : ∀ w ∈ ns, w.length = (d.stacks 4).length)
    (h10 : d.stacks 10 = []) (hs : ∀ j : Fin 20, 13 ≤ j.val → j.val ≤ 16 → d.stacks j = []) :
    ∃ e, Eval (readCached binomial)
      (i*(28*(d.stacks 4).length+34)+30*(d.stacks 4).length+43) d e ∧
      e.stacks = readResult d (ps.getD i []) (ns.getD i []) ∧
      e.regs 8 = d.regs 8 := by
  have htp : (ps.take i).length = i := List.length_take_of_le (Nat.le_of_lt hip)
  have htn : (ns.take i).length = i := List.length_take_of_le (Nat.le_of_lt hin)
  obtain ⟨e,he,hst,hr⟩ := readCached_eval binomial d (ps.take i) (ns.take i)
    (ps.getD i []) (ns.getD i []) (ps.drop (i+1)).flatten (ns.drop (i+1)).flatten
    (by rw [hp]; exact SubexponentialSAT.Subexp.GatherProgram.row_decomposition ps i hip)
    (by rw [hn]; exact SubexponentialSAT.Subexp.GatherProgram.row_decomposition ns i hin)
    (by omega) (by omega)
    (fun w hw => hwp w (List.mem_of_mem_take hw))
    (fun w hw => hwn w (List.mem_of_mem_take hw))
    (by rw [List.getD_eq_getElem _ _ hip]; exact hwp _ (List.getElem_mem hip))
    (by rw [List.getD_eq_getElem _ _ hin]; exact hwn _ (List.getElem_mem hin)) h10 hs
  exact ⟨e,by simpa only [hi] using he,hst,hr⟩

theorem readH_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool)
    (hu : c.Uniform) (hp : hindex.length < c.Hpositive.length)
    (hn : hindex.length < c.Hnegative.length) :
    ∃ r, r 8 = regs 8 ∧
      Eval (readCached false)
        (hindex.length*(28*c.width.length+34)+30*c.width.length+43)
        (cacheState c regs counter hindex kindex buffer queue parity)
        (cacheState c r counter hindex kindex buffer queue parity (c.Hword hindex.length)) := by
  let d := cacheState c regs counter hindex kindex buffer queue parity
  obtain ⟨e,he,hs,hr⟩ := readCached_get false d c.Hpositive c.Hnegative hindex.length
    rfl rfl rfl hp hn hu.1 hu.2.1 rfl (by
      intro j hj hj'
      fin_cases j <;> simp_all [d, cacheState])
  have heq : e = cacheState c e.regs counter hindex kindex buffer queue parity (c.Hword hindex.length) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hs]
    funext j
    fin_cases j <;> simp [readResult,d,cacheState,Cache.Hword]
  rw [heq] at he
  exact ⟨e.regs,hr,he⟩

theorem readB_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool)
    (hu : c.Uniform) (hp : kindex.length < c.Bpositive.length)
    (hn : kindex.length < c.Bnegative.length) :
    ∃ r, r 8 = regs 8 ∧
      Eval (readCached true)
        (kindex.length*(28*c.width.length+34)+30*c.width.length+43)
        (cacheState c regs counter hindex kindex buffer queue parity)
        (cacheState c r counter hindex kindex buffer queue parity (c.Bword kindex.length)) := by
  let d := cacheState c regs counter hindex kindex buffer queue parity
  obtain ⟨e,he,hs,hr⟩ := readCached_get true d c.Bpositive c.Bnegative kindex.length
    rfl rfl rfl hp hn hu.2.2.1 hu.2.2.2 rfl (by
      intro j hj hj'
      fin_cases j <;> simp_all [d, cacheState])
  have heq : e = cacheState c e.regs counter hindex kindex buffer queue parity (c.Bword kindex.length) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hs]
    funext j
    fin_cases j <;> simp [readResult,d,cacheState,Cache.Bword]
  rw [heq] at he
  exact ⟨e.regs,hr,he⟩

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramStep.lean

/-! One real triple-production iteration: two scans, three serializers and
paid cleanup. Only a parity bit is kept outside the subroutine registers. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

def selectedWord (c : Cache) (work : WordPair) (which : Fin 3) : WordPair :=
  if which = 0 then work else if which = 1 then (work.2,work.1) else c.power

theorem cacheEmit_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool) (work : WordPair) (which : Fin 3) :
    ∃ r, r 8 = regs 8 ∧
      Eval (emitCached which) (18*pairLength (selectedWord c work which)+39)
        (cacheState c regs counter hindex kindex buffer queue parity work)
        (cacheState c r counter hindex kindex
          ((LayoutScalarEmitter.record (selectedWord c work which).1
            (selectedWord c work which).2).reverse++buffer) queue parity work) := by
  let d := cacheState c regs counter hindex kindex buffer queue parity work
  obtain ⟨e,he,hs,hr⟩ := emitCached_eval which d (by
    intro j hj hj'
    fin_cases j <;> simp_all [d, cacheState])
  have hs1 : d.stacks (emitPorts which 0) = (selectedWord c work which).1 := by
    fin_cases which <;> rfl
  have hs2 : d.stacks (emitPorts which 1) = (selectedWord c work which).2 := by
    fin_cases which <;> rfl
  have heq : e = cacheState c e.regs counter hindex kindex
      ((LayoutScalarEmitter.record (selectedWord c work which).1
        (selectedWord c work which).2).reverse++buffer) queue parity work := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hs,hs1,hs2]
    funext j
    fin_cases j <;> simp [d,cacheState]
  rw [heq,hs1,hs2] at he
  exact ⟨e.regs,hr,he⟩

def clearWork : Code := .seq (.call (StackRoutines.clearProgram 11 0 1))
  (.call (StackRoutines.clearProgram 12 0 1))

theorem clearWork_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool) (work : WordPair) :
    Eval clearWork (2*pairLength work+6)
      (cacheState c regs counter hindex kindex buffer queue parity work)
      (cacheState c (readRegs regs 0 1 none) counter hindex kindex buffer queue parity) := by
  have h1 := SubexponentialSAT.Subexp.TupleProgram.clear_eval (11 : Fin 20) (0 : Fin 9) 1
    (cacheState c regs counter hindex kindex buffer queue parity work)
  have h2 := SubexponentialSAT.Subexp.TupleProgram.clear_eval (12 : Fin 20) (0 : Fin 9) 1
    (cacheState c (readRegs regs 0 1 none) counter hindex kindex buffer queue parity ([],work.2))
  have heq1 : StackRoutines.clearStacks 11
      (cacheState c regs counter hindex kindex buffer queue parity work).stacks =
      (cacheState c (readRegs regs 0 1 none) counter hindex kindex buffer queue parity ([],work.2)).stacks := by
    funext j
    fin_cases j <;> simp [StackRoutines.clearStacks,cacheState]
  have heq2 : StackRoutines.clearStacks 12
      (cacheState c (readRegs regs 0 1 none) counter hindex kindex buffer queue parity ([],work.2)).stacks =
      (cacheState c (readRegs regs 0 1 none) counter hindex kindex buffer queue parity).stacks := by
    funext j
    fin_cases j <;> simp [StackRoutines.clearStacks,cacheState]
  simp only [heq1] at h1
  simp only [heq2] at h2
  have hh := h1.seq h2
  convert hh using 1 <;> simp [clearWork,cacheState,pairLength,StackRoutines.readRegs_reset] ; ring

def wordRecord (w : WordPair) := LayoutScalarEmitter.record w.1 w.2

def cacheSignedEmit : Code := .seq emitSigned clearWork

theorem cacheSignedEmit_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool) (work : WordPair) :
    ∃ r, r 8 = regs 8 ∧
      Eval cacheSignedEmit (20*pairLength work+46)
        (cacheState c regs counter hindex kindex buffer queue parity work)
        (cacheState c r counter hindex kindex
          ((wordRecord (signedPair (regs 8) work.1 work.2)).reverse++buffer) queue parity) := by
  cases hg : regs 8
  · obtain ⟨r,hr,he⟩ := cacheEmit_eval c regs counter hindex kindex buffer queue parity work 0
    have hc := clearWork_eval c r counter hindex kindex
      ((wordRecord work).reverse++buffer) queue parity work
    refine ⟨readRegs r 0 1 none,by simpa [readRegs,hg] using hr,?_⟩
    have hh := (Eval.ite_false (yes := emitCached 1) (by simpa [cacheState] using hg) he).seq hc
    convert hh using 1 <;>
      simp [cacheSignedEmit,emitSigned,selectedWord,signedPair,wordRecord] ; ring
  · obtain ⟨r,hr,he⟩ := cacheEmit_eval c regs counter hindex kindex buffer queue parity work 1
    have hc := clearWork_eval c r counter hindex kindex
      ((wordRecord (work.2,work.1)).reverse++buffer) queue parity work
    refine ⟨readRegs r 0 1 none,by simpa [readRegs,hg] using hr,?_⟩
    have hh := (Eval.ite_true (no := emitCached 0) (by simpa [cacheState] using hg) he).seq hc
    convert hh using 1 <;>
      simp [cacheSignedEmit,emitSigned,selectedWord,signedPair,wordRecord,pairLength] ; ring

def cachePlainEmit : Code := .seq (emitCached 0) clearWork

theorem cachePlainEmit_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool) (work : WordPair) :
    ∃ r, r 8 = regs 8 ∧
      Eval cachePlainEmit (20*pairLength work+45)
        (cacheState c regs counter hindex kindex buffer queue parity work)
        (cacheState c r counter hindex kindex ((wordRecord work).reverse++buffer) queue parity) := by
  obtain ⟨r,hr,he⟩ := cacheEmit_eval c regs counter hindex kindex buffer queue parity work 0
  have hc := clearWork_eval c r counter hindex kindex ((wordRecord work).reverse++buffer) queue parity work
  refine ⟨readRegs r 0 1 none,by simpa [readRegs] using hr,?_⟩
  convert he.seq hc using 1 <;> simp [cachePlainEmit,selectedWord] ; ring

def advance : Code := .seq (.base (.atom (.bnot 8 8)))
  (.seq (.base (.atom (.set 0 true))) (.base (.atom (.push 9 0))))

theorem advance_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool) :
    ∃ r, r 8 = !(regs 8) ∧ Eval advance 3
      (cacheState c regs counter hindex kindex buffer queue parity)
      (cacheState c r counter hindex (true::kindex) buffer queue parity) := by
  let d := cacheState c regs counter hindex kindex buffer queue parity
  let a := (StructuredProgram.Atom.bnot (8 : Fin 9) 8).eval d
  let b := (StructuredProgram.Atom.set (0 : Fin 9) true).eval a
  let e := (StructuredProgram.Atom.push (9 : Fin 20) (0 : Fin 9)).eval b
  have h1 : Eval (.base (.atom (.bnot 8 8))) 1 d a := .base (.atom _ _)
  have h2 : Eval (.base (.atom (.set 0 true))) 1 a b := .base (.atom _ _)
  have h3 : Eval (.base (.atom (.push 9 0))) 1 b e := .base (.atom _ _)
  have hr : e.regs 8 = !(regs 8) := by
    simp [e,b,a,d,cacheState,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr]
  have heq : e = cacheState c e.regs counter hindex (true::kindex) buffer queue parity := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;>
      simp [b,a,d,cacheState,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr]
  have hall : Eval advance 3 d e := h1.seq (h2.seq h3)
  rw [heq] at hall
  exact ⟨e.regs,hr,hall⟩

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramBody.lean

/-! A fixed, paid iteration producing the three real scalar operands. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

abbrev Triple := WordPair × WordPair × WordPair

/-- The scalar consumer uses this same three-word order definitionally. -/
def tripleWords (xs : List Triple) : List WordPair :=
  xs.flatMap fun x => [x.1,x.2.1,x.2.2]

def triple (c : Cache) (sign : Bool) (h k : ℕ) : Triple :=
  (signedPair sign (c.Hword h).1 (c.Hword h).2,c.power,c.Bword k)

def tripleRecord (t : Triple) : List Bool :=
  wordRecord t.1 ++ wordRecord t.2.1 ++ wordRecord t.2.2

def popH : Code := .base (.atom (.pop 8 0 1))

def body : Code := .seq popH (.seq (readCached false) (.seq cacheSignedEmit
  (.seq (emitCached 2) (.seq (readCached true) (.seq cachePlainEmit advance)))))

def bodyCost (m k W P : ℕ) := (m+k)*(28*W+34)+140*W+18*P+220

theorem Cache.Hword_length (c : Cache) (hu : c.Uniform) (i : ℕ)
    (hp : i < c.Hpositive.length) (hn : i < c.Hnegative.length) :
    pairLength (c.Hword i) = 2*c.width.length := by
  have h1 := hu.1 (c.Hpositive[i]) (List.getElem_mem hp)
  have h2 := hu.2.1 (c.Hnegative[i]) (List.getElem_mem hn)
  simp only [Cache.Hword,pairLength,List.getD_eq_getElem _ _ hp,List.getD_eq_getElem _ _ hn]
  omega

theorem Cache.Bword_length (c : Cache) (hu : c.Uniform) (i : ℕ)
    (hp : i < c.Bpositive.length) (hn : i < c.Bnegative.length) :
    pairLength (c.Bword i) = 2*c.width.length := by
  have h1 := hu.2.2.1 (c.Bpositive[i]) (List.getElem_mem hp)
  have h2 := hu.2.2.2 (c.Bnegative[i]) (List.getElem_mem hn)
  simp only [Cache.Bword,pairLength,List.getD_eq_getElem _ _ hp,List.getD_eq_getElem _ _ hn]
  omega

theorem popH_eval (c : Cache) (regs : Fin 9 → Bool) (b : Bool)
    (counter hindex kindex buffer queue parity : List Bool) :
    Eval popH 1 (cacheState c regs counter (b::hindex) kindex buffer queue parity)
      (cacheState c (readRegs regs 0 1 (some b)) counter hindex kindex buffer queue parity) := by
  have h : Eval popH 1 (cacheState c regs counter (b::hindex) kindex buffer queue parity)
    ((StructuredProgram.Atom.pop (8 : Fin 20) (0 : Fin 9) 1).eval
      (cacheState c regs counter (b::hindex) kindex buffer queue parity)) := .base (.atom _ _)
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;>
      simp [cacheState,StructuredProgram.Atom.instr,execInstr]

theorem body_eval (c : Cache) (regs : Fin 9 → Bool) (b : Bool)
    (counter hindex kindex buffer queue parity : List Bool)
    (hu : c.Uniform)
    (hhp : hindex.length < c.Hpositive.length) (hhn : hindex.length < c.Hnegative.length)
    (hbp : kindex.length < c.Bpositive.length) (hbn : kindex.length < c.Bnegative.length) :
    ∃ r, r 8 = !(regs 8) ∧
      Eval body (bodyCost hindex.length kindex.length c.width.length (pairLength c.power))
        (cacheState c regs counter (b::hindex) kindex buffer queue parity)
        (cacheState c r counter hindex (true::kindex)
          ((tripleRecord (triple c (regs 8) hindex.length kindex.length)).reverse++buffer)
          queue parity) := by
  let r0 := readRegs regs 0 1 (some b)
  have hp := popH_eval c regs b counter hindex kindex buffer queue parity
  obtain ⟨r1,hr1,h1⟩ := readH_eval c r0 counter hindex kindex buffer queue parity hu hhp hhn
  obtain ⟨r2,hr2,h2⟩ := cacheSignedEmit_eval c r1 counter hindex kindex buffer queue parity
    (c.Hword hindex.length)
  have hr10 : r1 8 = regs 8 := by simpa [r0,readRegs] using hr1
  rw [hr10] at h2
  let Hrec := wordRecord (signedPair (regs 8) (c.Hword hindex.length).1 (c.Hword hindex.length).2)
  let PRec := wordRecord c.power
  let BRec := wordRecord (c.Bword kindex.length)
  obtain ⟨r3,hr3,h3⟩ := cacheEmit_eval c r2 counter hindex kindex (Hrec.reverse++buffer)
    queue parity ([],[]) 2
  simp only [selectedWord,show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide,
    ↓reduceIte] at h3
  obtain ⟨r4,hr4,h4⟩ := readB_eval c r3 counter hindex kindex
    (PRec.reverse++(Hrec.reverse++buffer)) queue parity hu hbp hbn
  obtain ⟨r5,hr5,h5⟩ := cachePlainEmit_eval c r4 counter hindex kindex
    (PRec.reverse++(Hrec.reverse++buffer)) queue parity (c.Bword kindex.length)
  obtain ⟨r6,hr6,h6⟩ := advance_eval c r5 counter hindex kindex
    (BRec.reverse++(PRec.reverse++(Hrec.reverse++buffer))) queue parity
  have h56 := h5.seq h6
  have h456 := h4.seq h56
  have h3456 := h3.seq h456
  have h23456 := h2.seq h3456
  have h123456 := h1.seq h23456
  have hall := hp.seq h123456
  have hlh := c.Hword_length hu hindex.length hhp hhn
  have hlb := c.Bword_length hu kindex.length hbp hbn
  rw [hlh,hlb] at hall
  have ht : 1 + ((hindex.length*(28*c.width.length+34)+30*c.width.length+43) +
      ((20*(2*c.width.length)+46) + ((18*pairLength c.power+39) +
        ((kindex.length*(28*c.width.length+34)+30*c.width.length+43) +
          ((20*(2*c.width.length)+45)+3))))) =
      bodyCost hindex.length kindex.length c.width.length (pairLength c.power) := by
    unfold bodyCost
    ring
  have hout : BRec.reverse++(PRec.reverse++(Hrec.reverse++buffer)) =
      (tripleRecord (triple c (regs 8) hindex.length kindex.length)).reverse++buffer := by
    simp only [tripleRecord,triple,Hrec,PRec,BRec,wordRecord,List.reverse_append,List.append_assoc]
  rw [ht,hout] at hall
  refine ⟨r6,by rw [hr6,hr5,hr4,hr3,hr2,hr10],?_⟩
  simpa only [body] using hall

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramLoop.lean

/-! The native unary loop produces all triples in increasing binomial index. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open SubexponentialSAT.Subexp.MatrixParityProgram (toggle)

def preparedTriples (c : Cache) : Bool → ℕ → ℕ → List Triple
  | _,0,_ => []
  | sign,n+1,k => triple c sign n k :: preparedTriples c (!sign) n (k+1)

def preparedRecords (c : Cache) (sign : Bool) (n k : ℕ) : List Bool :=
  (preparedTriples c sign n k).flatMap tripleRecord

@[simp] theorem preparedTriples_length (c : Cache) (s : Bool) (n k : ℕ) :
    (preparedTriples c s n k).length = n := by
  induction n generalizing s k with
  | zero => rfl
  | succ n ih => simp [preparedTriples,ih]

def popCount : Code := .base (.atom (.pop 7 6 7))
def loop : Code := .seq popCount (.while 7 (.seq body popCount))

def loopCost : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0,_,_,_ => 2
  | n+1,k,W,P => bodyCost n k W P + 2 + loopCost n (k+1) W P

theorem popCount_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool) :
    Eval popCount 1 (cacheState c regs counter hindex kindex buffer queue parity)
      (cacheState c (readRegs regs 6 7 counter.head?) counter.tail hindex kindex buffer queue parity) := by
  have h : Eval popCount 1 (cacheState c regs counter hindex kindex buffer queue parity)
    ((StructuredProgram.Atom.pop (7 : Fin 20) (6 : Fin 9) 7).eval
      (cacheState c regs counter hindex kindex buffer queue parity)) := .base (.atom _ _)
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;>
      simp [cacheState,StructuredProgram.Atom.instr,execInstr]

theorem eval_seq_decompose {first second : Code} {t : ℕ} {a z : Data}
    (h : Eval (.seq first second) t a z) :
    ∃ t₁ t₂ mid, t = t₁+t₂ ∧ Eval first t₁ a mid ∧ Eval second t₂ mid z := by
  cases h with
  | seq h₁ h₂ => exact ⟨_,_,_,rfl,h₁,h₂⟩

theorem loop_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool)
    (hu : c.Uniform) (hf : c.Fits (counter.length+kindex.length))
    (hlen : hindex.length = counter.length) :
    ∃ r, r 8 = toggle counter.length (regs 8) ∧
      Eval loop (loopCost counter.length kindex.length c.width.length (pairLength c.power))
        (cacheState c regs counter hindex kindex buffer queue parity)
        (cacheState c r [] [] (List.replicate counter.length true++kindex)
          ((preparedRecords c (regs 8) counter.length kindex.length).reverse++buffer) queue parity) := by
  induction counter generalizing regs hindex kindex buffer with
  | nil =>
    have hh : hindex = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst hindex
    let r := readRegs regs 6 7 none
    have hp := popCount_eval c regs [] [] kindex buffer queue parity
    have hr : r 7 = false := by simp [r,readRegs]
    refine ⟨r,by simp [r,readRegs,toggle],?_⟩
    have hw : Eval (.while 7 (.seq body popCount)) 1
        (cacheState c r [] [] kindex buffer queue parity)
        (cacheState c r [] [] kindex buffer queue parity) := .while_false hr
    simpa [loop,loopCost,preparedRecords,preparedTriples,r] using hp.seq hw
  | cons cb counter ih =>
    cases hindex with
    | nil => simp at hlen
    | cons hb hindex =>
      have hlen' : hindex.length = counter.length := by simpa using hlen
      let r0 := readRegs regs 6 7 (some cb)
      have hr0 : r0 8 = regs 8 := by simp [r0,readRegs]
      have hg : r0 7 = true := by simp [r0,readRegs]
      have hp := popCount_eval c regs (cb::counter) (hb::hindex) kindex buffer queue parity
      have hhp : hindex.length < c.Hpositive.length := by have := hf.1; simp only [List.length_cons] at this; omega
      have hhn : hindex.length < c.Hnegative.length := by have := hf.2.1; simp only [List.length_cons] at this; omega
      have hbp : kindex.length < c.Bpositive.length := by have := hf.2.2.1; simp only [List.length_cons] at this; omega
      have hbn : kindex.length < c.Bnegative.length := by have := hf.2.2.2; simp only [List.length_cons] at this; omega
      obtain ⟨r1,hr1,hs⟩ := body_eval c r0 hb counter hindex kindex buffer queue parity hu hhp hhn hbp hbn
      have hf' : c.Fits (counter.length+(true::kindex).length) := by
        simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hf
      obtain ⟨r2,hr2,ht⟩ := ih r1 hindex (true::kindex)
        ((tripleRecord (triple c (r0 8) hindex.length kindex.length)).reverse++buffer) hf' hlen'
      obtain ⟨t₁,t₂,mid,htime,htp,htw⟩ := eval_seq_decompose ht
      refine ⟨r2,?_,?_⟩
      · rw [hr2,hr1,hr0]
        rfl
      · have hall := hp.seq (Eval.while_true (test := 7)
          (show (cacheState c r0 counter (hb::hindex) kindex buffer queue parity).regs 7 = true
            from hg) (hs.seq htp) htw)
        have hcost : 1 + ((bodyCost hindex.length kindex.length c.width.length
              (pairLength c.power)+t₁)+t₂+1) =
            loopCost (cb::counter).length kindex.length c.width.length (pairLength c.power) := by
          simp only [List.length_cons] at htime
          simp only [List.length_cons,loopCost,hlen']
          omega
        rw [hcost,hr1,hr0] at hall
        simpa [loop,preparedRecords,preparedTriples,hlen',List.flatMap_cons,List.reverse_append,
          List.replicate_succ',List.append_assoc] using hall

theorem loopCost_le (n k W P : ℕ) :
    loopCost n k W P ≤ n*((n+k)*(28*W+34)+140*W+18*P+222)+2 := by
  induction n generalizing k with
  | zero => simp [loopCost]
  | succ n ih =>
    have ht := ih (k+1)
    simp only [loopCost,bodyCost]
    nlinarith

theorem preparedRecords_encoding (c : Cache) (sign : Bool) (n k : ℕ) :
    pairEncoding (tripleWords (preparedTriples c sign n k)) =
      preparedRecords c sign n k ++ [false] := by
  have h : ∀ xs : List Triple,
      pairEncoding (tripleWords xs) = xs.flatMap tripleRecord ++ [false] := by
    intro xs
    induction xs with
    | nil => rfl
    | cons t xs ih =>
      change pairEncoding (t.1::t.2.1::t.2.2::tripleWords xs) =
        (tripleRecord t ++ xs.flatMap tripleRecord) ++ [false]
      simp only [pairEncoding]
      rw [ih]
      simp [tripleRecord,wordRecord,LayoutScalarEmitter.record,
        RowSelectionProgram.Entries.pairPrefix,List.append_assoc]
  exact h _

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramFinish.lean

/-! Initial unary copy/parity and final stream reversal are native paid calls. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open SubexponentialSAT.Subexp.MatrixParityProgram (toggle)

def parityRegisters : Fin 3 → Fin 9 := ![0,1,8]
def parityPorts : Fin 1 → Fin 20 := fun _ => 19

theorem parityRegisters_injective : Function.Injective parityRegisters := by decide
theorem parityPorts_injective : Function.Injective parityPorts := by decide

def parityCall : Code := .call (ProgramLinking.liftProgram
  SubexponentialSAT.Subexp.MatrixParityProgram.program parityRegisters parityPorts)

theorem parityCall_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool) :
    ∃ r, r 8 = toggle parity.length (regs 8) ∧
      Eval parityCall (3*parity.length+3)
        (cacheState c regs counter hindex kindex buffer queue parity)
        (cacheState c r counter hindex kindex buffer queue []) := by
  let d := cacheState c regs counter hindex kindex buffer queue parity
  let a := projectState parityRegisters parityPorts d
  let b : State 3 1 := ⟨![false,false,toggle parity.length (regs 8)],fun _ => []⟩
  have ht : Trace SubexponentialSAT.Subexp.MatrixParityProgram.program (3*parity.length+3)
      (a.withPC (some SubexponentialSAT.Subexp.MatrixParityProgram.program.entry)) (b.withPC none) := by
    have hstart : a.withPC (some SubexponentialSAT.Subexp.MatrixParityProgram.program.entry) =
        SubexponentialSAT.Subexp.MatrixParityProgram.start a.regs parity := by
      congr 1
    have ha2 : a.regs 2 = regs 8 := rfl
    rw [hstart]
    simpa [b, SubexponentialSAT.Subexp.MatrixParityProgram.finish,
      StructuredProgram.State.withPC, ha2] using
      SubexponentialSAT.Subexp.MatrixParityProgram.program_trace a.regs parity
  let e := embedState parityRegisters parityPorts d b
  have he := eval_call_from_state SubexponentialSAT.Subexp.MatrixParityProgram.program
    parityRegisters parityPorts d parityRegisters_injective parityPorts_injective ht
  have hr : e.regs 8 = toggle parity.length (regs 8) := by
    have h := embedState_register parityRegisters parityPorts d b parityRegisters_injective 2
    simpa [e,parityRegisters,b] using h
  have hbs : b.stacks = Function.update a.stacks 0 [] := by funext j; fin_cases j; rfl
  have hst : e.stacks = Function.update d.stacks 19 [] := by
    change Function.extend parityPorts b.stacks d.stacks = _
    rw [hbs,ProgramLinking.extend_update parityPorts_injective]
    have hf := congrArg StructuredProgram.State.stacks
      (embedState_project parityRegisters parityPorts d parityRegisters_injective parityPorts_injective)
    change Function.extend parityPorts a.stacks d.stacks = d.stacks at hf
    rw [hf]
    rfl
  have heq : e = cacheState c e.regs counter hindex kindex buffer queue [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    change e.stacks = _
    rw [hst]
    funext j
    fin_cases j <;> simp [d,cacheState]
  exact ⟨e.regs,hr,by simpa only [parityCall,← heq] using he⟩

def initializeTriples : Code := .seq (.call (StackRoutines.copyProgram 7 8 10 0 1))
  (.seq (.base (.atom (.set 8 false))) parityCall)

theorem initializeTriples_eval (c : Cache) (regs : Fin 9 → Bool) (counter parity : List Bool) :
    ∃ r, r 8 = toggle parity.length false ∧
      Eval initializeTriples (7*counter.length+3*parity.length+9)
        (cacheState c regs counter [] [] [] [] parity)
        (cacheState c r counter counter [] [] [] []) := by
  let d := cacheState c regs counter [] [] [] [] parity
  have hc := StackRoutines.halt_after_trace _
    (StackRoutines.copyProgram_trace (7 : Fin 20) 8 10 (0 : Fin 9) 1
      (by decide) (by decide) (by decide) (by decide) d.regs d.stacks rfl) 7 rfl rfl
  let r0 := readRegs regs 0 1 none
  have hcopy : Eval (.call (StackRoutines.copyProgram 7 8 10 0 1)) (7*counter.length+5)
      d (cacheState c r0 counter counter [] [] [] parity) := by
    apply Eval.call
    convert hc using 1 <;>
      simp [d,r0,cacheState,StackRoutines.copyResult,
        StructuredProgram.State.withPC,StackRoutines.copyStacks,Nat.add_assoc]
    funext j
    fin_cases j <;> simp
  let r1 := Function.update r0 8 false
  have hset : Eval (.base (.atom (.set 8 false))) 1
      (cacheState c r0 counter counter [] [] [] parity)
      (cacheState c r1 counter counter [] [] [] parity) := by
    exact .base (.atom _ _)
  obtain ⟨r,hr,hp⟩ := parityCall_eval c r1 counter counter [] [] [] parity
  refine ⟨r,by simpa [r1] using hr,?_⟩
  convert hcopy.seq (hset.seq hp) using 1
  · rfl
  · ring

def finishPorts : Fin 7 → Fin 20 := ![0,1,17,13,14,15,18]
theorem finishPorts_injective : Function.Injective finishPorts := by decide

def finish : Code := liftCommand LayoutScalarEmitter.finishList 2 6 workRegisters finishPorts

theorem finish_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer parity : List Bool) :
    ∃ r, Eval finish (3*buffer.length+9)
      (cacheState c regs counter hindex kindex buffer [] parity)
      (cacheState c r counter hindex kindex [] (buffer.reverse++[false]) parity) := by
  let d := cacheState c regs counter hindex kindex buffer [] parity
  let a := projectState workRegisters finishPorts d
  obtain ⟨b,hb,hbs⟩ := LayoutScalarEmitter.finishList_eval a rfl
  let e := embedState workRegisters finishPorts d b
  have he := eval_liftCommand_from_state LayoutScalarEmitter.finishList 2 6
    workRegisters finishPorts d workRegisters_injective finishPorts_injective hb
  have hst : e.stacks = Function.update (Function.update d.stacks 17 []) 18
      (buffer.reverse++[false]) := by
    change Function.extend finishPorts b.stacks d.stacks = _
    rw [hbs,ProgramLinking.extend_update finishPorts_injective,
      ProgramLinking.extend_update finishPorts_injective]
    have hf := congrArg StructuredProgram.State.stacks
      (embedState_project workRegisters finishPorts d workRegisters_injective finishPorts_injective)
    change Function.extend finishPorts a.stacks d.stacks = d.stacks at hf
    rw [hf]
    rfl
  have heq : e = cacheState c e.regs counter hindex kindex [] (buffer.reverse++[false]) parity := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    change e.stacks = _
    rw [hst]
    funext j
    fin_cases j <;> simp [d,cacheState]
  change Eval _ _ d e at he
  rw [heq] at he
  refine ⟨e.regs,?_⟩
  simpa [finish,a,d,projectState,finishPorts,cacheState,Nat.add_assoc] using he

def clearIndex : Code := .call (StackRoutines.clearProgram 9 0 1)

theorem clearIndex_eval (c : Cache) (regs : Fin 9 → Bool) (kindex queue : List Bool) :
    Eval clearIndex (2*kindex.length+3)
      (cacheState c regs [] [] kindex [] queue [])
      (cacheState c (readRegs regs 0 1 none) [] [] [] [] queue []) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.clear_eval (9 : Fin 20) (0 : Fin 9) 1
    (cacheState c regs [] [] kindex [] queue [])
  have hs : StackRoutines.clearStacks 9 (cacheState c regs [] [] kindex [] queue []).stacks =
      (cacheState c regs [] [] [] [] queue []).stacks := by
    funext j
    fin_cases j <;> simp [StackRoutines.clearStacks,cacheState]
  rw [hs] at h
  simpa [clearIndex,cacheState] using h

def prepare : Code := .seq initializeTriples (.seq loop (.seq finish clearIndex))
def prepareProgram := compiled prepare 7 18

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgram.lean

/-! Complete cache-to-triple primitive program with all scans and copies paid. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open SubexponentialSAT.Subexp.MatrixParityProgram (toggle)

theorem signedPair_length (s : Bool) (p n : List Bool) :
    pairLength (signedPair s p n) = p.length+n.length := by
  cases s <;> simp [signedPair,pairLength,Nat.add_comm]

theorem tripleRecord_length (c : Cache) (s : Bool) (n k : ℕ)
    (hu : c.Uniform) (hhp : n < c.Hpositive.length) (hhn : n < c.Hnegative.length)
    (hbp : k < c.Bpositive.length) (hbn : k < c.Bnegative.length) :
    (tripleRecord (triple c s n k)).length = 8*c.width.length+2*pairLength c.power+9 := by
  have hh := c.Hword_length hu n hhp hhn
  have hb := c.Bword_length hu k hbp hbn
  simp only [tripleRecord,triple,List.length_append,wordRecord,LayoutScalarEmitter.record_length]
  change ((2*pairLength (signedPair s (c.Hword n).1 (c.Hword n).2)+3)+
    (2*pairLength c.power+3))+(2*pairLength (c.Bword k)+3) = _
  rw [signedPair_length]
  change ((2*pairLength (c.Hword n)+3)+(2*pairLength c.power+3))+(2*pairLength (c.Bword k)+3) = _
  rw [hh,hb]
  ring

theorem preparedRecords_length (c : Cache) (s : Bool) (n k : ℕ)
    (hu : c.Uniform) (hf : c.Fits (n+k)) :
    (preparedRecords c s n k).length = n*(8*c.width.length+2*pairLength c.power+9) := by
  induction n generalizing s k with
  | zero => simp [preparedRecords,preparedTriples]
  | succ n ih =>
    have ht := tripleRecord_length c s n k hu (by have := hf.1; omega)
      (by have := hf.2.1; omega) (by have := hf.2.2.1; omega) (by have := hf.2.2.2; omega)
    have hf' : c.Fits (n+(k+1)) := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hf
    have hi := ih (!s) (k+1) hf'
    simp only [preparedRecords,preparedTriples,List.flatMap_cons,List.length_append] at ht hi ⊢
    rw [ht,hi]
    ring

def prepareCost (N A W P : ℕ) : ℕ :=
  9*N+3*A+loopCost N 0 W P+3*(N*(8*W+2*P+9))+21

/-- The only nonempty input stacks are the retained caches, width, power,
the unary number of terms, and the unary parity exponent. -/
theorem prepare_eval (c : Cache) (regs : Fin 9 → Bool) (counter parity : List Bool)
    (hu : c.Uniform) (hf : c.Fits counter.length) :
    ∃ r, Eval prepare (prepareCost counter.length parity.length c.width.length (pairLength c.power))
      (cacheState c regs counter [] [] [] [] parity)
      (cacheState c r [] [] [] []
        (pairEncoding (tripleWords
          (preparedTriples c (toggle parity.length false) counter.length 0))) []) := by
  obtain ⟨r0,hr0,hi⟩ := initializeTriples_eval c regs counter parity
  obtain ⟨r1,hr1,hl⟩ := loop_eval c r0 counter counter [] [] [] [] hu
    (by simpa using hf) rfl
  rw [hr0] at hl
  simp only [List.length_nil,List.append_nil] at hl
  let records := preparedRecords c (toggle parity.length false) counter.length 0
  obtain ⟨r2,hf2⟩ := finish_eval c r1 [] [] (List.replicate counter.length true) records.reverse []
  have hc := clearIndex_eval c r2 (List.replicate counter.length true)
    (records.reverse.reverse++[false])
  have hlen : records.length = counter.length*(8*c.width.length+2*pairLength c.power+9) :=
    preparedRecords_length c _ _ _ hu (by simpa using hf)
  have hencoding : records++[false] =
      pairEncoding (tripleWords
        (preparedTriples c (toggle parity.length false) counter.length 0)) :=
    (preparedRecords_encoding c _ _ _).symm
  have hfinish := hf2.seq hc
  have hloop := hl.seq hfinish
  have hall := hi.seq hloop
  simp only [List.length_reverse,List.length_replicate,hlen,List.reverse_reverse,hencoding] at hall
  have ht : (7*counter.length+3*parity.length+9) +
      (loopCost counter.length 0 c.width.length (pairLength c.power) +
        ((3*(counter.length*(8*c.width.length+2*pairLength c.power+9))+9) +
          (2*counter.length+3))) =
      prepareCost counter.length parity.length c.width.length (pairLength c.power) := by
    unfold prepareCost
    ring
  rw [ht] at hall
  refine ⟨readRegs r2 0 1 none,?_⟩
  simpa only [prepare] using hall

theorem prepareCost_le (N A W P : ℕ) :
    prepareCost N A W P ≤
      9*N+3*A+N*(N*(28*W+34)+140*W+18*P+222)+3*(N*(8*W+2*P+9))+23 := by
  have h := loopCost_le N 0 W P
  simp only [Nat.add_zero] at h
  unfold prepareCost
  omega

/-- A concrete finite program, including its final halt, with no arithmetic
oracle in the transition relation. All original cache words are retained. -/
theorem prepareProgram_runsIn (c : Cache) (regs : Fin 9 → Bool) (counter parity : List Bool)
    (hu : c.Uniform) (hf : c.Fits counter.length) :
    ∃ r, RunsIn prepareProgram
      (9*counter.length+3*parity.length+
        counter.length*(counter.length*(28*c.width.length+34)+140*c.width.length+
          18*pairLength c.power+222)+
        3*(counter.length*(8*c.width.length+2*pairLength c.power+9))+24)
      ((cacheState c regs counter [] [] [] [] parity).withPC (some prepareProgram.entry))
      ((cacheState c r [] [] [] []
        (pairEncoding (tripleWords
          (preparedTriples c (toggle parity.length false) counter.length 0))) []).withPC none) := by
  obtain ⟨r,he⟩ := prepare_eval c regs counter parity hu hf
  refine ⟨r,⟨_,?_,compiled_halt_trace he 7 18⟩⟩
  have h := prepareCost_le counter.length parity.length c.width.length (pairLength c.power)
  omega

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
