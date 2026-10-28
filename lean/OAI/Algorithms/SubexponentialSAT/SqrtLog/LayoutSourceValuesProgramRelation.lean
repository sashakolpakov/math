import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgramLoop

namespace OAI.Algorithms

/-! Relational refinement of the same table builder. Each scalar may have any
correct byte representation; all table entries are obtained from executions. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open _root_.OAI.Algorithms.SubexponentialSAT.SubexpPolynomialServiceControl (transfer transfer_run)
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Every observed callback result is a measured scalar computation. -/
def CallbackRelation (callback : Code) (base : Store)
    (valid : ℕ → List Bool → Prop) (Q K W : ℕ) : Prop :=
  ∀ j, j < Q → ∀ remaining acc regs, ∃ n rf word,
    n ≤ K ∧ word.length = W ∧ valid j word ∧
    Eval callback n (⟨regs,loopState base j remaining acc⟩ : Data)
      (⟨rf,Function.update (loopState base j remaining acc) 255 word⟩ : Data)

theorem append_scalar_run (base : Store) (j : ℕ) (remaining acc word : List Bool)
    (h255 : base 255 = []) :
    ExecutesIn (.seq (transfer 255 65) advance) (3*word.length+5)
      (Function.update (loopState base j remaining acc) 255 word)
      (loopState base (j+1) remaining (word.reverse ++ acc)) := by
  let s1 := Function.update (loopState base j remaining acc) 255 word
  let s2 := loopState base j remaining (word.reverse ++ acc)
  have he2 : Function.update (Function.update s1 255 []) 65
      ((s1 255).reverse ++ s1 65) = s2 := by
    funext i
    by_cases h37 : i = 37 <;> by_cases h64 : i = 64 <;>
      by_cases h65 : i = 65 <;> by_cases hi255 : i = 255 <;>
      simp [s2,s1,loopState,Function.update_apply,h37,h64,h65,hi255,h255]
  have h2 : ExecutesIn (transfer 255 65) (3*word.length+3) s1 s2 := by
    have h := transfer_run 255 65 s1 (by decide)
    rw [he2] at h
    simpa [s1] using h
  have h3 : ExecutesIn advance 2 s2
      (loopState base (j+1) remaining (word.reverse ++ acc)) := by
    intro regs
    refine ⟨2,Function.update regs 0 true,le_rfl,?_⟩
    have h := Subexp.TupleProgram.pushConst_eval (37 : Fin 256) (0 : Fin 16) true
      (⟨regs,s2⟩ : Data)
    have he : Function.update s2 37 (true :: s2 37) =
        loopState base (j+1) remaining (word.reverse ++ acc) := by
      funext i
      by_cases h37 : i = 37 <;> by_cases h64 : i = 64 <;> by_cases h65 : i = 65 <;>
        simp [s2,loopState,h37,h64,h65,List.replicate_succ]
    simpa only [advance,Subexp.TupleProgram.pushedState,he] using h
  exact (h2.seq h3).mono (by omega)

theorem loop_visits_relation (callback : Code) (base : Store)
    (valid : ℕ → List Bool → Prop) (Q K W : ℕ)
    (spec : CallbackRelation callback base valid Q K W) (h255 : base 255 = [])
    (remaining acc : List Bool) (j : ℕ) (hj : j + remaining.length ≤ Q)
    (regs : Fin 16 → Bool) :
    ∃ (words : List (List Bool)) (costs : List ℕ) (n : ℕ) (rf : Fin 16 → Bool),
      words.length = remaining.length ∧
      (∀ word ∈ words, word.length = W) ∧
      List.Forall₂ valid (List.range' j remaining.length) words ∧
      n ≤ remaining.length*(K+3*W+7)+2 ∧
      UnaryForPrograms.Visits ports (body callback) costs n
        (⟨regs,loopState base j remaining acc⟩ : Data)
        (⟨rf,loopState base (j+remaining.length) []
          (words.flatten.reverse ++ acc)⟩ : Data) := by
  induction remaining generalizing j acc regs with
  | nil =>
    refine ⟨[],[],2,readRegs regs 14 15 none,rfl,by simp,by simp,by simp,?_⟩
    simpa only [popped_loopState,List.head?_nil,List.tail_nil,List.length_nil,
      Nat.add_zero,List.flatten_nil,List.reverse_nil,List.nil_append] using
      UnaryForPrograms.Visits.done (p := ports) (body := body callback)
        (⟨regs,loopState base j [] acc⟩ : Data) (by simp [loopState,ports])
  | cons bit remaining ih =>
    obtain ⟨nc,rc,word,hnc,hw,hv,hc⟩ := spec j
      (by simp only [List.length_cons] at hj; omega) remaining acc
      (readRegs regs 14 15 (some bit))
    obtain ⟨na,ra,hna,ha⟩ := append_scalar_run base j remaining acc word h255 rc
    have hb : Eval (body callback) (nc+na)
        (⟨readRegs regs 14 15 (some bit),loopState base j remaining acc⟩ : Data)
        (⟨ra,loopState base (j+1) remaining (word.reverse ++ acc)⟩ : Data) := hc.seq ha
    obtain ⟨words,costs,nt,rt,hl,hws,hvs,hnt,ht⟩ := ih (word.reverse ++ acc) (j+1)
      (by simp only [List.length_cons] at hj; omega) ra
    refine ⟨word::words,(nc+na)::costs,nc+na+nt+2,rt,by simp [hl],?_,?_,?_,?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hw
      · exact hws x hx
    · simpa only [List.length_cons,List.range'_succ] using List.Forall₂.cons hv hvs
    · simp only [List.length_cons]
      rw [hw] at hna
      nlinarith
    · have h := UnaryForPrograms.Visits.step (p := ports) (body := body callback)
        (d := (⟨regs,loopState base j (bit::remaining) acc⟩ : Data))
        (by simp [loopState,ports])
        (by simpa only [popped_loopState,List.head?_cons,List.tail_cons] using hb)
        (by simp [loopState,ports,UnaryForPrograms.popped]) ht
      simpa only [List.length_cons,List.flatten_cons,List.reverse_append,List.append_assoc,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem command_relation (callback : Code) (base : Store)
    (valid : ℕ → List Bool → Prop) (Q K W : ℕ)
    (spec : CallbackRelation callback base valid Q K W) (hQ : (base 22).length = Q)
    (h37 : base 37 = []) (h64 : base 64 = []) (h65 : base 65 = [])
    (h67 : base 67 = []) (h120 : base 120 = []) (h255 : base 255 = [])
    (regs : Fin 16 → Bool) :
    ∃ (words : List (List Bool)) (n : ℕ) (rf : Fin 16 → Bool),
      words.length = Q ∧ (∀ word ∈ words, word.length = W) ∧
      List.Forall₂ valid (List.range' 0 Q) words ∧
      n ≤ Q*(K+6*W+16)+13 ∧
      Eval (command callback) n (⟨regs,base⟩ : Data)
        (⟨rf,Function.update base 67 words.flatten⟩ : Data) := by
  let s1 := loopState base 0 (base 22) []
  have he1 : Function.update base 64 (base 22 ++ base 64) = s1 := by
    funext i
    by_cases hi37 : i = 37 <;> by_cases hi64 : i = 64 <;> by_cases hi65 : i = 65 <;>
      simp [s1,loopState,hi37,hi64,hi65,h37,h64,h65]
  obtain ⟨n1,r1,hn1,e1⟩ := copy_run 22 64 base (by decide) (by decide) (by decide) h120 regs
  rw [he1] at e1
  obtain ⟨words,costs,n2,r2,hl,hws,hvs,hn2,hv⟩ := loop_visits_relation callback base valid
    Q K W spec h255 (base 22) [] 0 (by omega) r1
  simp only [hQ,Nat.zero_add,List.append_nil] at hl hvs hn2 hv
  let s2 := loopState base Q [] words.flatten.reverse
  let s3 := Function.update s2 37 []
  have e2 : Eval (loop callback) n2 (⟨r1,s1⟩ : Data) (⟨r2,s2⟩ : Data) := hv.eval
  obtain ⟨n3,r3,hn3,e3⟩ := clear_run 37 s2 r2
  have he4 : Function.update (Function.update s3 65 []) 67
      ((s3 65).reverse ++ s3 67) = Function.update base 67 words.flatten := by
    funext i
    by_cases hi37 : i = 37 <;> by_cases hi64 : i = 64 <;>
      by_cases hi65 : i = 65 <;> by_cases hi67 : i = 67 <;>
      simp [s3,s2,loopState,hi37,hi64,hi65,hi67,h37,h64,h65,h67]
  obtain ⟨n4,r4,hn4,e4⟩ := transfer_run 65 67 s3 (by decide) r3
  rw [he4] at e4
  have hflat : words.flatten.length = Q*W := by
    rw [List.length_flatten]
    have hm : words.map List.length = words.map (fun _ => W) := by
      apply List.map_congr_left
      exact hws
    rw [hm]
    simp [hl]
  refine ⟨words,n1+(n2+(n3+n4)),r4,hl,hws,hvs,?_,e1.seq (e2.seq (e3.seq e4))⟩
  simp only [hQ] at hn1
  have hs2 : (s2 37).length = Q := by simp [s2,loopState]
  have hs3 : (s3 65).length = Q*W := by simp [s3,s2,loopState,hflat]
  rw [hs2] at hn3
  rw [hs3] at hn4
  nlinarith

theorem program_relation (callback : Code) (base : Store)
    (valid : ℕ → List Bool → Prop) (Q K W : ℕ)
    (spec : CallbackRelation callback base valid Q K W) (hQ : (base 22).length = Q)
    (h37 : base 37 = []) (h64 : base 64 = []) (h65 : base 65 = [])
    (h67 : base 67 = []) (h120 : base 120 = []) (h255 : base 255 = [])
    (regs : Fin 16 → Bool) :
    ∃ (words : List (List Bool)) (rf : Fin 16 → Bool),
      words.length = Q ∧ (∀ word ∈ words, word.length = W) ∧
      List.Forall₂ valid (List.range' 0 Q) words ∧
      RunsIn (program callback) (Q*(K+6*W+16)+14)
        ((⟨regs,base⟩ : Data).withPC (some (program callback).entry))
        ((⟨rf,Function.update base 67 words.flatten⟩ : Data).withPC none) := by
  obtain ⟨words,n,rf,hl,hw,hv,hn,he⟩ := command_relation callback base valid Q K W spec hQ
    h37 h64 h65 h67 h120 h255 regs
  exact ⟨words,rf,hl,hw,hv,n+1,by omega,compiled_halt_trace he 22 67⟩

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

end OAI.Algorithms
