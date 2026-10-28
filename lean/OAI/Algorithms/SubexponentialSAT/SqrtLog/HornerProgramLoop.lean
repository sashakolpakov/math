import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgramControl

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update lowFrame_refl)

abbrev backward := @SubexpHornerControl.backward
abbrev fold := @SubexpHornerControl.fold

def ready {C : Type*} (base : Store) (encode : C → List Bool)
    (cs : List C) (a : C) (count : List Bool) : Store :=
  Function.update (Function.update (Function.update base 246 (backward encode cs))
    240 (encode a)) 248 count

def counterPorts : UnaryForPrograms.Ports 16 256 := ⟨248, 0, 1⟩

def traversal (body : Code) : Code := UnaryForPrograms.forCmd counterPorts body

theorem popped_ready {C : Type*} (base : Store) (encode : C → List Bool)
    (cs : List C) (a : C) (count : List Bool) (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped counterPorts (⟨regs, ready base encode cs a count⟩ : Data) =
      (⟨readRegs regs 0 1 count.head?, ready base encode cs a count.tail⟩ : Data) := by
  apply state_ext
  · simp [UnaryForPrograms.popped, counterPorts, ready]
  · simp [UnaryForPrograms.popped, counterPorts, ready]

theorem traversal_visits {C : Type*} (base : Store) (encode : C → List Bool)
    (body : Code) (step : C → C → C) (K : ℕ)
    (hstep : ∀ c cs a count, ExecutesIn body K
      (ready base encode (c :: cs) a count)
      (ready base encode cs (step a c) count))
    (cs : List C) (a : C) (count : List Bool) (hlen : count.length = cs.length)
    (regs : Fin 16 → Bool) :
    ∃ costs n regs',
      UnaryForPrograms.Visits counterPorts body costs n
        (⟨regs, ready base encode cs a count⟩ : Data)
        (⟨regs', ready base encode [] (fold step cs a) []⟩ : Data) ∧
      n ≤ cs.length * (K + 2) + 2 := by
  induction cs generalizing count a regs with
  | nil =>
      have hc : count = [] := List.length_eq_zero_iff.mp hlen
      subst count
      refine ⟨[], 2, readRegs regs 0 1 none, ?_, by simp⟩
      simpa only [popped_ready, List.head?_nil, List.tail_nil, fold,
        SubexpHornerControl.fold] using
        UnaryForPrograms.Visits.done (p := counterPorts) (body := body)
          (⟨regs, ready base encode [] a []⟩ : Data) (by simp [ready, counterPorts])
  | cons c cs ih =>
      cases count with
      | nil => simp at hlen
      | cons bit count =>
          have hl : count.length = cs.length := by simpa using hlen
          obtain ⟨nb, rb, hnb, hb⟩ := hstep c cs a count (readRegs regs 0 1 (some bit))
          obtain ⟨costs, nt, rt, ht, hnt⟩ := ih (step a c) count hl rb
          refine ⟨nb :: costs, nb + nt + 2, rt, ?_, ?_⟩
          · have h := UnaryForPrograms.Visits.step
              (p := counterPorts) (body := body)
              (d := (⟨regs, ready base encode (c :: cs) a (bit :: count)⟩ : Data))
              (by simp [ready, counterPorts])
              (by simpa only [popped_ready, List.head?_cons, List.tail_cons] using hb)
              (by simp [ready, counterPorts, UnaryForPrograms.popped]) ht
            simpa only [fold, SubexpHornerControl.fold] using h
          · simp only [List.length_cons]
            nlinarith

theorem traversal_run {C : Type*} (base : Store) (encode : C → List Bool)
    (body : Code) (step : C → C → C) (K : ℕ)
    (hstep : ∀ c cs a count, ExecutesIn body K
      (ready base encode (c :: cs) a count)
      (ready base encode cs (step a c) count))
    (cs : List C) (a : C) (count : List Bool) (hlen : count.length = cs.length) :
    ExecutesIn (traversal body) (cs.length * (K + 2) + 2)
      (ready base encode cs a count)
      (ready base encode [] (fold step cs a) []) := by
  intro regs
  obtain ⟨costs, n, rf, ht, hn⟩ := traversal_visits base encode body step K
    hstep cs a count hlen regs
  exact ⟨n, rf, hn, ht.eval⟩

theorem streaming_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length = W)
    (x : C) (hx : base 247 = encode x) (hw : (base 250).length = W)
    (h120 : base 120 = []) (h241 : base 241 = []) (h244 : base 244 = [])
    (h245 : base 245 = []) (h251 : base 251 = []) (h252 : base 252 = [])
    (cs : List C) (a : C) (count : List Bool) (hlen : count.length = cs.length) :
    ExecutesIn (traversal (iteration multiply add))
      (cs.length * (Km + Ka + 50 * W + 49) + 2)
      (ready base encode cs a count)
      (ready base encode [] (fold (stepValue mulOp addOp x) cs a) []) := by
  apply traversal_run base encode (iteration multiply add) (stepValue mulOp addOp x)
    (Km + Ka + 50 * W + 47) _ cs a count hlen
  intro c cs a count
  let s := ready base encode (c :: cs) a count
  have hf : LowFrame base s := lowFrame_update
    (lowFrame_update (lowFrame_update (lowFrame_refl base) 246 (by decide) _)
      240 (by decide) _) 248 (by decide) _
  have h := iteration_run base encode multiply add mulOp addOp Km Ka W hm ha hwidth
    s a x c (backward encode cs) hf
    (by simp [s, ready]) (by simp [s, ready, hx])
    (by simp [s, ready, backward, SubexpHornerControl.backward])
    (by simp [s, ready, hw])
    (by simp [s, ready, h120]) (by simp [s, ready, h241])
    (by simp [s, ready, h244]) (by simp [s, ready, h245])
    (by simp [s, ready, h251]) (by simp [s, ready, h252])
  convert h using 1
  funext i
  by_cases h240 : i = 240 <;> by_cases h246 : i = 246 <;>
    by_cases h248 : i = 248 <;>
    simp [s, ready, h240, h246, h248]

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
