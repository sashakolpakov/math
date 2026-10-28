import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutBounds

namespace OAI.Algorithms

/-! Selected output words of the actual complete layout execution. -/

namespace SubexponentialSAT.SubexpMainLayoutOutputBounds

open SubexpMainProgram SubexpSetupProgram SubexpPackingParameters
open SubexpMainLayoutWordBounds

variable {cfg : Config} {er n : ℕ} [NeZero (r n)]
variable {alloc : SubexpLayoutPorts.Allocation (mainExtraStacks cfg)} {hregs : 16 ≤ er}
variable {a : MainState er (mainExtraStacks cfg)} {G : SubexpLeafData.Leaf n}
variable {input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G}
variable {ready : DyadicSchedule.Ready cfg.k cfg.T n}

/-- Every selected output word is bounded through the actual trace. This
excludes the pending stream, and supplies the next phase's stored inputs. -/
theorem seed_output_bound (actual : SubexpMainScheduledLayout.Run alloc hregs a G input ready)
    (valid : SubexpMainAssembly.validLeaf cfg n G) (W : ℕ) (ha : RelevantWordBound W a) :
    RelevantWordBound ((SubexpMainLayoutBounds.constant cfg.k+1)*
      (SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W
        (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))+1)^
          SubexpMainLayoutBounds.exponent) actual.out := by
  let X := SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W
    (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))
  have hW : W ≤ X := by dsimp only [X, SubexpMainLayoutSeedBounds.seed]; omega
  have hx : X+1 ≤ (X+1)^SubexpMainLayoutBounds.exponent :=
    Nat.le_self_pow (Nat.ne_of_gt (SubexpMainLayoutPolynomial.degree_pos _ _)) _
  have ht : actual.steps ≤ SubexpMainLayoutBounds.constant cfg.k*
      (X+1)^SubexpMainLayoutBounds.exponent :=
    SubexpMainLayoutBounds.seed_bound actual valid W ha
  apply mono (after_eval ha actual.trace)
  change W+actual.steps ≤ (SubexpMainLayoutBounds.constant cfg.k+1)*
    (X+1)^SubexpMainLayoutBounds.exponent
  rw [Nat.add_mul, one_mul]
  omega

end SubexponentialSAT.SubexpMainLayoutOutputBounds

end OAI.Algorithms
