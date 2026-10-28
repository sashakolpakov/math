import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainInvariant
import OAI.Algorithms.SubexponentialSAT.SubexpMainController
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutProgram
import OAI.Algorithms.SubexponentialSAT.SubexpMainMoments
import OAI.Algorithms.SubexponentialSAT.SubexpMainCRT

namespace OAI.Algorithms

/-!
# The fixed six-phase program

The setup configuration and finite workspace are selected from the clause
width before reading an input. Every phase below is a concrete finite
program. The execution and uniform time bound are separate obligations.
-/

namespace SubexponentialSAT.SubexpMainFixedProgram

open StructuredCalls SubexpMainProgram SubexpSetupProgram

def allocation (cfg : Config) (hsize : 672 ≤ helperSize cfg) :
    SubexpLayoutPorts.Allocation (mainExtraStacks cfg) :=
  ⟨helperSize cfg, hsize, SubexpMainInvariant.helper_within cfg⟩

def crtAllocation (cfg : Config) (hsize : 672 ≤ helperSize cfg) :
    SubexpMainCRT.Allocation (mainExtraStacks cfg) :=
  ⟨helperSize cfg, by omega, SubexpMainInvariant.helper_within cfg⟩

theorem enough_registers (er : ℕ) (hr : 16 ≤ er) : 32 ≤ workRegs er := by
  dsimp [workRegs]
  omega

noncomputable def phases (cfg : Config) (hsize : 672 ≤ helperSize cfg)
    (er : ℕ) (hr : 16 ≤ er) :
    Phases er (mainExtraStacks cfg) where
  setup := mainProcedure cfg er
  sparsify := SubexpActualSparsify.procedure cfg (enough_registers er hr)
  layout := SubexpMainLayoutProgram.procedure er hr (allocation cfg hsize)
  moments := SubexpMainMoments.procedure er (allocation cfg hsize)
  crt := SubexpMainCRT.procedure er (crtAllocation cfg hsize)
  decode := SubexpMainReady.procedure er (mainExtraStacks cfg) (helperSize cfg)
    (SubexpMainInvariant.helper_within cfg)

noncomputable def leaf (cfg : Config) (hsize : 672 ≤ helperSize cfg)
    (er : ℕ) (hr : 16 ≤ er) :
    MainCmd er (mainExtraStacks cfg) :=
  SubexpEmptyClauseGuard.leafCallback (phases cfg hsize er hr)

noncomputable def command (cfg : Config) (hsize : 672 ≤ helperSize cfg)
    (er : ℕ) (hr : 16 ≤ er) :
    MainCmd er (mainExtraStacks cfg) :=
  SubexpMainController.command (phases cfg hsize er hr) (leaf cfg hsize er hr)

noncomputable def program (cfg : Config) (hsize : 672 ≤ helperSize cfg)
    (er : ℕ) (hr : 16 ≤ er) :=
  SubexpMainController.program (phases cfg hsize er hr) (leaf cfg hsize er hr)

noncomputable def primitive (cfg : Config) (hsize : 672 ≤ helperSize cfg) (er : ℕ) (hr : 16 ≤ er) :=
  BitProgram.primitive (program cfg hsize er hr)

theorem primitive_execution (cfg : Config) (hsize : 672 ≤ helperSize cfg)
    (er : ℕ) (hr : 16 ≤ er) {input : List Bool} {steps : ℕ}
    {final : MainState er (mainExtraStacks cfg)} {answer : Bool}
    (trace : Eval (command cfg hsize er hr) steps
      (initialData er (mainExtraStacks cfg) input) final)
    (output : (final.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 11)).head? =
      some answer) :
    (primitive cfg hsize er hr).OutputsInTime input answer
      (BitProgram.primitiveOverhead (program cfg hsize er hr) * (steps + 1)) := by
  apply BitProgram.primitive_outputs_of_halted (program cfg hsize er hr)
    ⟨steps + 1, le_rfl, SubexpMainController.compiled_execution trace⟩ rfl
  exact output

/-- A sufficiently large fixed allocation exists for each eligible clause
width. Its choice does not depend on an input formula or variable count. -/
theorem configuration_exists (k : ℕ) (hk : 2 ≤ k) :
    ∃ cfg : Config, cfg.k = k ∧ 672 ≤ helperSize cfg := by
  obtain ⟨cfg, hwidth, hextra⟩ := config_exists k 672 hk
  refine ⟨cfg, hwidth, ?_⟩
  dsimp [helperSize]
  omega

end SubexponentialSAT.SubexpMainFixedProgram

end OAI.Algorithms
