import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialServiceControl
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! Fixed control that constructs an ordered scalar table. The callback is an
actual finite command with a measured execution contract. Runtime unary node
indices and counters do not change the command. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open _root_.OAI.Algorithms.SubexponentialSAT.SubexpPolynomialServiceControl (transfer transfer_run)

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Node37, remaining64, reversed table65; all other bytes are caller state. -/
def loopState (base : Store) (j : ℕ) (remaining acc : List Bool) : Store :=
  Function.update (Function.update (Function.update base 37 (List.replicate j true))
    64 remaining) 65 acc

def values (value : ℕ → List Bool) (j n : ℕ) : List Bool :=
  ((List.range' j n).map value).flatten

@[simp] theorem values_zero (value : ℕ → List Bool) (j : ℕ) :
    values value j 0 = [] := by simp [values]

theorem values_succ (value : ℕ → List Bool) (j n : ℕ) :
    values value j (n+1) = value j ++ values value (j+1) n := by
  simp [values, List.range'_succ]

theorem values_length (value : ℕ → List Bool) (W : ℕ)
    (hw : ∀ j, (value j).length = W) (j n : ℕ) :
    (values value j n).length = n * W := by
  induction n generalizing j with
  | zero => simp
  | succ n ih => rw [values_succ, List.length_append, hw, ih]; ring

def ports : UnaryForPrograms.Ports 16 256 := ⟨64,14,15⟩
def advance : Code := Subexp.TupleProgram.pushConst 37 0 true

def body (callback : Code) : Code :=
  .seq callback (.seq (transfer 255 65) advance)
def loop (callback : Code) : Code := UnaryForPrograms.forCmd ports (body callback)

def command (callback : Code) : Code :=
  .seq (copy 22 64) (.seq (loop callback) (.seq (clear 37) (transfer 65 67)))
def program (callback : Code) := compiled (command callback) 22 67

/-- Only a traced finite callback may establish each scalar. -/
def CallbackSpec (callback : Code) (base : Store) (value : ℕ → List Bool)
    (Q K : ℕ) : Prop :=
  ∀ j, j < Q → ∀ remaining acc,
    ExecutesIn callback K (loopState base j remaining acc)
      (Function.update (loopState base j remaining acc) 255 (value j))

theorem body_run (callback : Code) (base : Store) (value : ℕ → List Bool)
    (Q K W : ℕ) (spec : CallbackSpec callback base value Q K)
    (hw : ∀ j, (value j).length = W) (h255 : base 255 = [])
    (j : ℕ) (hj : j < Q) (remaining acc : List Bool) :
    ExecutesIn (body callback) (K + 3*W + 5) (loopState base j remaining acc)
      (loopState base (j+1) remaining ((value j).reverse ++ acc)) := by
  let s := loopState base j remaining acc
  let s1 := Function.update s 255 (value j)
  let s2 := loopState base j remaining ((value j).reverse ++ acc)
  have h1 : ExecutesIn callback K s s1 := spec j hj remaining acc
  have he2 : Function.update (Function.update s1 255 []) 65
      ((s1 255).reverse ++ s1 65) = s2 := by
    funext i
    by_cases h37 : i = 37 <;> by_cases h64 : i = 64 <;>
      by_cases h65 : i = 65 <;> by_cases hi255 : i = 255 <;>
      simp [s2,s1,s,loopState,h37,h64,h65,hi255,h255]
  have h2 : ExecutesIn (transfer 255 65) (3*W+3) s1 s2 := by
    have h := transfer_run 255 65 s1 (by decide)
    rw [he2] at h
    simpa [s1,hw] using h
  have h3 : ExecutesIn advance 2 s2
      (loopState base (j+1) remaining ((value j).reverse ++ acc)) := by
    intro regs
    refine ⟨2,Function.update regs 0 true,le_rfl,?_⟩
    have h := Subexp.TupleProgram.pushConst_eval (37 : Fin 256) (0 : Fin 16) true
      (⟨regs,s2⟩ : Data)
    have he : Function.update s2 37 (true :: s2 37) =
        loopState base (j+1) remaining ((value j).reverse ++ acc) := by
      funext i
      by_cases h37 : i = 37 <;> by_cases h64 : i = 64 <;> by_cases h65 : i = 65 <;>
        simp [s2,loopState,h37,h64,h65,List.replicate_succ]
    simpa only [advance,Subexp.TupleProgram.pushedState,he] using h
  exact (h1.seq (h2.seq h3)).mono (by omega)

theorem popped_loopState (base : Store) (j : ℕ) (remaining acc : List Bool)
    (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped ports (⟨regs,loopState base j remaining acc⟩ : Data) =
      (⟨readRegs regs 14 15 remaining.head?,
        loopState base j remaining.tail acc⟩ : Data) := by
  apply SubexpScanPrimitives.state_ext
  · simp [UnaryForPrograms.popped,ports,loopState]
  · funext i
    by_cases h37 : i = 37 <;> by_cases h64 : i = 64 <;> by_cases h65 : i = 65 <;>
      simp [UnaryForPrograms.popped,ports,loopState,h37,h64,h65]

theorem loop_visits (callback : Code) (base : Store) (value : ℕ → List Bool)
    (Q K W : ℕ) (spec : CallbackSpec callback base value Q K)
    (hw : ∀ j, (value j).length = W) (h255 : base 255 = [])
    (remaining acc : List Bool) (j : ℕ) (hj : j + remaining.length ≤ Q)
    (regs : Fin 16 → Bool) :
    ∃ costs n rf, n ≤ remaining.length * (K+3*W+7)+2 ∧
      UnaryForPrograms.Visits ports (body callback) costs n
        (⟨regs,loopState base j remaining acc⟩ : Data)
        (⟨rf,loopState base (j+remaining.length) []
          ((values value j remaining.length).reverse ++ acc)⟩ : Data) := by
  induction remaining generalizing j acc regs with
  | nil =>
    refine ⟨[],2,readRegs regs 14 15 none,by simp,?_⟩
    simpa only [popped_loopState,List.head?_nil,List.tail_nil,List.length_nil,
      Nat.add_zero,values_zero,List.reverse_nil,List.nil_append] using
      UnaryForPrograms.Visits.done (p := ports) (body := body callback)
        (⟨regs,loopState base j [] acc⟩ : Data) (by simp [loopState,ports])
  | cons b remaining ih =>
    obtain ⟨nb,rb,hnb,hb⟩ := body_run callback base value Q K W spec hw h255
      j (by simp only [List.length_cons] at hj; omega) remaining acc
      (readRegs regs 14 15 (some b))
    obtain ⟨costs,nt,rt,hnt,ht⟩ := ih ((value j).reverse ++ acc) (j+1)
      (by simp only [List.length_cons] at hj; omega) rb
    refine ⟨nb::costs,nb+nt+2,rt,?_,?_⟩
    · simp only [List.length_cons]; nlinarith
    · have h := UnaryForPrograms.Visits.step (p := ports) (body := body callback)
        (d := (⟨regs,loopState base j (b::remaining) acc⟩ : Data))
        (by simp [loopState,ports])
        (by simpa only [popped_loopState,List.head?_cons,List.tail_cons] using hb)
        (by simp [loopState,ports,UnaryForPrograms.popped]) ht
      simpa only [List.length_cons,values_succ,List.reverse_append,List.append_assoc,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem loop_run (callback : Code) (base : Store) (value : ℕ → List Bool)
    (Q K W : ℕ) (spec : CallbackSpec callback base value Q K)
    (hw : ∀ j, (value j).length = W) (h255 : base 255 = [])
    (remaining acc : List Bool) (j : ℕ) (hj : j + remaining.length ≤ Q) :
    ExecutesIn (loop callback) (remaining.length*(K+3*W+7)+2)
      (loopState base j remaining acc)
      (loopState base (j+remaining.length) []
        ((values value j remaining.length).reverse ++ acc)) := by
  intro regs
  obtain ⟨costs,n,rf,hn,he⟩ := loop_visits callback base value Q K W spec hw h255
    remaining acc j hj regs
  exact ⟨n,rf,hn,he.eval⟩

theorem command_run (callback : Code) (base : Store) (value : ℕ → List Bool)
    (Q K W : ℕ) (spec : CallbackSpec callback base value Q K)
    (hw : ∀ j, (value j).length = W) (hQ : (base 22).length = Q)
    (h37 : base 37 = []) (h64 : base 64 = []) (h65 : base 65 = [])
    (h67 : base 67 = []) (h120 : base 120 = []) (h255 : base 255 = []) :
    ExecutesIn (command callback) (Q*(K+6*W+16)+13) base
      (Function.update base 67 (values value 0 Q)) := by
  let s1 := loopState base 0 (base 22) []
  let s2 := loopState base Q [] (values value 0 Q).reverse
  let s3 := Function.update s2 37 []
  have he1 : Function.update base 64 (base 22 ++ base 64) = s1 := by
    funext i
    by_cases hi37 : i = 37 <;> by_cases hi64 : i = 64 <;> by_cases hi65 : i = 65 <;>
      simp [s1,loopState,hi37,hi64,hi65,h37,h64,h65]
  have h1 : ExecutesIn (copy 22 64) (7*Q+5) base s1 := by
    have h := copy_run 22 64 base (by decide) (by decide) (by decide) h120
    rw [he1,hQ] at h
    exact h
  have h2 : ExecutesIn (loop callback) (Q*(K+3*W+7)+2) s1 s2 := by
    have h := loop_run callback base value Q K W spec hw h255 (base 22) [] 0 (by omega)
    simpa only [s1,s2,hQ,Nat.zero_add,List.append_nil] using h
  have h3 : ExecutesIn (clear 37) (2*Q+3) s2 s3 := by
    have h := clear_run 37 s2
    simpa [s2,loopState,s3] using h
  have he4 : Function.update (Function.update s3 65 []) 67
      ((s3 65).reverse ++ s3 67) = Function.update base 67 (values value 0 Q) := by
    funext i
    by_cases hi37 : i = 37 <;> by_cases hi64 : i = 64 <;>
      by_cases hi65 : i = 65 <;> by_cases hi67 : i = 67 <;>
      simp [s3,s2,loopState,hi37,hi64,hi65,hi67,h37,h64,h65,h67]
  have h4 : ExecutesIn (transfer 65 67) (3*(Q*W)+3) s3
      (Function.update base 67 (values value 0 Q)) := by
    have h := transfer_run 65 67 s3 (by decide)
    rw [he4] at h
    simpa [s3,s2,loopState,values_length value W hw] using h
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by ring_nf; omega)

theorem program_runsIn (callback : Code) (base : Store) (value : ℕ → List Bool)
    (Q K W : ℕ) (spec : CallbackSpec callback base value Q K)
    (hw : ∀ j, (value j).length = W) (hQ : (base 22).length = Q)
    (h37 : base 37 = []) (h64 : base 64 = []) (h65 : base 65 = [])
    (h67 : base 67 = []) (h120 : base 120 = []) (h255 : base 255 = [])
    (regs : Fin 16 → Bool) :
    ∃ rf, RunsIn (program callback) (Q*(K+6*W+16)+14)
      ((⟨regs,base⟩ : Data).withPC (some (program callback).entry))
      ((⟨rf,Function.update base 67 (values value 0 Q)⟩ : Data).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_run callback base value Q K W spec hw hQ
    h37 h64 h65 h67 h120 h255 regs
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 22 67⟩

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

end OAI.Algorithms
