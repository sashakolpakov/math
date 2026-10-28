import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgramLoop

namespace OAI.Algorithms

/-! A native bounded traversal with distinct input cells and output accumulator.
This is used to construct the padded polynomial-cell stream before Horner. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Traversal
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

variable {C : Type*}

def ready (base : Store) (encode : C → List Bool)
    (cs : List C) (acc count : List Bool) : Store :=
  Function.update (Function.update (Function.update base 246
    (HornerProgram.backward encode cs)) 240 acc) 248 count

def command (body : Code) : Code := HornerProgram.traversal body

theorem popped_ready (base : Store) (encode : C → List Bool)
    (cs : List C) (acc count : List Bool) (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped HornerProgram.counterPorts
      (⟨regs, ready base encode cs acc count⟩ : Data) =
      (⟨readRegs regs 0 1 count.head?, ready base encode cs acc count.tail⟩ : Data) := by
  apply state_ext
  · simp [UnaryForPrograms.popped, HornerProgram.counterPorts, ready]
  · simp [UnaryForPrograms.popped, HornerProgram.counterPorts, ready]

theorem visits (base : Store) (encode : C → List Bool)
    (body : Code) (step : List Bool → C → List Bool) (K : ℕ)
    (hstep : ∀ c cs acc count, ExecutesIn body K
      (ready base encode (c :: cs) acc count)
      (ready base encode cs (step acc c) count))
    (cs : List C) (acc count : List Bool) (hlen : count.length = cs.length)
    (regs : Fin 16 → Bool) :
    ∃ costs n regs', UnaryForPrograms.Visits HornerProgram.counterPorts body costs n
      (⟨regs, ready base encode cs acc count⟩ : Data)
      (⟨regs', ready base encode [] (cs.foldl step acc) []⟩ : Data) ∧
      n ≤ cs.length * (K + 2) + 2 := by
  induction cs generalizing count acc regs with
  | nil =>
      have hc : count = [] := List.length_eq_zero_iff.mp hlen
      subst count
      refine ⟨[], 2, readRegs regs 0 1 none, ?_, by simp⟩
      simpa only [popped_ready, List.head?_nil, List.tail_nil, List.foldl_nil] using
        UnaryForPrograms.Visits.done (p := HornerProgram.counterPorts) (body := body)
          (⟨regs, ready base encode [] acc []⟩ : Data)
          (by simp [ready, HornerProgram.counterPorts])
  | cons c cs ih =>
      cases count with
      | nil => simp at hlen
      | cons bit count =>
          have hl : count.length = cs.length := by simpa using hlen
          obtain ⟨nb, rb, hnb, hb⟩ := hstep c cs acc count (readRegs regs 0 1 (some bit))
          obtain ⟨costs, nt, rt, ht, hnt⟩ := ih (step acc c) count hl rb
          refine ⟨nb :: costs, nb + nt + 2, rt, ?_, ?_⟩
          · have h := UnaryForPrograms.Visits.step
              (p := HornerProgram.counterPorts) (body := body)
              (d := (⟨regs, ready base encode (c :: cs) acc (bit :: count)⟩ : Data))
              (by simp [ready, HornerProgram.counterPorts])
              (by simpa only [popped_ready, List.head?_cons, List.tail_cons] using hb)
              (by simp [ready, HornerProgram.counterPorts, UnaryForPrograms.popped]) ht
            simpa only [List.foldl_cons] using h
          · simp only [List.length_cons]
            nlinarith

theorem run (base : Store) (encode : C → List Bool)
    (body : Code) (step : List Bool → C → List Bool) (K : ℕ)
    (hstep : ∀ c cs acc count, ExecutesIn body K
      (ready base encode (c :: cs) acc count)
      (ready base encode cs (step acc c) count))
    (cs : List C) (acc count : List Bool) (hlen : count.length = cs.length) :
    ExecutesIn (command body) (cs.length * (K + 2) + 2)
      (ready base encode cs acc count)
      (ready base encode [] (cs.foldl step acc) []) := by
  intro regs
  obtain ⟨costs, n, rf, ht, hn⟩ := visits base encode body step K hstep cs acc count hlen regs
  exact ⟨n, rf, hn, ht.eval⟩

end SubexponentialSAT.SqrtLog.PerturbationProgram.Traversal

end OAI.Algorithms
