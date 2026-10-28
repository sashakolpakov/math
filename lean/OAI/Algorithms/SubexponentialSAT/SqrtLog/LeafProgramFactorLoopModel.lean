import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactor
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramBoundsCapacity
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramRelModel

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop
open SubexponentialSAT BitProgram StructuredCalls MomentsProgram
open IdempotentApplyProgram.Bounds

abbrev Raw (n B d : ℕ) := List (Product.Entry n B d)

def state {n B d : ℕ} (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (seed : Raw n B d) (source payload : List Bool) : Factor.Data :=
  ⟨regs,Function.update (Function.update (Function.update base 151 (Product.bytes seed))
    150 source) 149 payload⟩

def recordState {n B d : ℕ} (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (seed : Raw n B d) (v pr f : Bool) (source payload : List Bool) : Factor.Data :=
  RecordPrograms.state Factor.ports (state base regs seed [] []) v pr f source payload

/-- One actual ID callback. The accumulator is existential at every call;
only its relation to the preceding accumulator is fixed. -/
def CallbackContract {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 768 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ) : Prop :=
  ∀ base, ready base → ∀ id seed tail regs, eligible id →
    Good Finset.univ u J seed → tail.length ≤ T →
    ∃ out, Good Finset.univ u J out ∧ step seed id out ∧
      ∃ k ≤ C, ∃ rr,
        Eval Factor.callback k
          (state base regs seed tail (Encoding.encodeNat id).reverse)
          (state base rr out tail []) ∧ rr 13=false ∧ rr 14=true ∧ rr 15=false

abbrev RunRel {n B d : ℕ} (step : Raw n B d → ℕ → Raw n B d → Prop) :=
  MomentsAssembly.Relational.FoldRel step

def records (ids : List ℕ) : List (List Bool) := ids.map Encoding.encodeNat

def loopBudget (C : ℕ) (ids : List ℕ) : ℕ :=
  RecordPrograms.budget (fun _ => C) (records ids)+3
end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop

end OAI.Algorithms
