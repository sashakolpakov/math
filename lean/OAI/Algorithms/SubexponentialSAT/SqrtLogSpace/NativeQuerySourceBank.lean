import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeAddressedQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad

/-! Actual addressed parked-bank readback from native query preparation. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query

/-- The physical parked bank contains the actual addressed plans and packing
output. The node field is supplied by the concrete node-counter load. -/
theorem sourceBank_of_parked (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (base front : Data) (l : Fin 8 → ℕ) (bw : Bank.Words)
    (hf : FrontState q k base front l bw)
    (first : MulticolorTypes.Word (packingProblem q k hg).r (packingProblem q k hg).Q)
    (rest : List (MulticolorTypes.Word (packingProblem q k hg).r (packingProblem q k hg).Q))
    (node : Fin (packingProblem q k hg).Q) (a : State 40 896)
    (hpark : ∀ i : Fin 14,
      a.stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i)) =
        (PackingCallerProgram.result front (packingProblem q k hg) first rest).stacks
          (LeafProgram.LayoutMasters.high i))
    (hnode : a.stacks 307 = LeafHeadSetupProgram.unary node.val) :
    NativeLayoutLoad.SourceBank
      (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first rest node) a := by
  let p := packingProblem q k hg
  let m := Execute.guardedModel (q.input k) l
  have he := packing_empty front hf.privateEmpty hf.spare
  have hp (i : Fin 14) (h5 : i ≠ 5) (h7 : i ≠ 7) (h8 : i ≠ 8) :
      a.stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i)) =
        front.stacks (LeafProgram.LayoutMasters.low i) :=
    (hpark i).trans (PackingCallerProgram.result_parameter front p he first rest i h5 h7 h8)
  have hn := (LeafQueryFrontend.exported_input_values (q.input k) l front hf.exported).1
  have hN := (LeafQueryFrontend.exported_input_values (q.input k) l front hf.exported).2.1
  have hr : m.val 18 = (produce (q.input k)).r := Execute.guardedModel_radius _ _
  have hQ : m.val 21 = (produce (q.input k)).Q :=
    (Execute.guardedModel_public (q.input k) l 4).trans
      (Layout.model_core_values (q.input k) l).2.2.2.2.1
  have hR : m.val 29 = (produce (q.input k)).R :=
    (Execute.guardedModel_public (q.input k) l 6).trans
      (Layout.model_core_values (q.input k) l).2.2.2.2.2.2.1
  have hu (i : Fin 8) := hf.exported.1 i
  constructor
  · exact (hp 0 (by decide) (by decide) (by decide)).trans hn
  · apply (hp 1 (by decide) (by decide) (by decide)).trans
    change front.stacks 129 = List.replicate p.factors true
    simpa only [p, packing_factors_eq] using hN
  · apply (hp 2 (by decide) (by decide) (by decide)).trans
    change front.stacks 130 = _
    simpa [Exports.destination, Exports.unaryValues, hr, m,
      LeafHeadSetupProgram.Native.queryInputsAddressed, LeafHeadSetupProgram.Native.queryInputs,
      LeafHeadSetupProgram.unary, packingProblem] using hu 2
  · apply (hp 3 (by decide) (by decide) (by decide)).trans
    change front.stacks 131 = _
    simpa [Exports.destination, Exports.unaryValues, hQ, m,
      LeafHeadSetupProgram.Native.queryInputsAddressed, LeafHeadSetupProgram.Native.queryInputs,
      LeafHeadSetupProgram.unary, packingProblem] using hu 3
  · apply (hp 4 (by decide) (by decide) (by decide)).trans
    change front.stacks 132 = _
    simpa [Exports.destination, Exports.unaryValues, hr, hQ, m,
      LeafHeadSetupProgram.Native.queryInputsAddressed, LeafHeadSetupProgram.Native.queryInputs,
      LeafHeadSetupProgram.unary, packingProblem] using hu 4
  · exact (hpark 5).trans (PackingCallerProgram.result_words front p he first rest)
  · exact (hp 6 (by decide) (by decide) (by decide)).trans hf.low
  · exact (hpark 7).trans (PackingCallerProgram.result_metadata front p he first rest)
  · exact (hpark 8).trans ((PackingCallerProgram.result_plans front p he first rest).trans
      (LeafHeadSetupProgram.Native.queryInputsAddressed_stream q k hg first rest node).symm)
  · apply (hp 10 (by decide) (by decide) (by decide)).trans
    change front.stacks 138 = _
    simpa [Exports.destination, Exports.unaryValues, hR, m,
      LeafHeadSetupProgram.Native.queryInputsAddressed, LeafHeadSetupProgram.Native.queryInputs,
      LeafHeadSetupProgram.unary] using hu 5
  · apply (hp 11 (by decide) (by decide) (by decide)).trans
    change front.stacks 139 = _
    simpa [Exports.destination, Exports.unaryValues, hr, hQ, hR, m,
      LeafHeadSetupProgram.Native.queryInputsAddressed, LeafHeadSetupProgram.Native.queryInputs,
      LeafHeadSetupProgram.unary] using hu 6
  · apply (hp 12 (by decide) (by decide) (by decide)).trans
    change front.stacks 140 = _
    simpa [Exports.destination, Exports.unaryValues, hr, hQ, hR, m,
      LeafHeadSetupProgram.Native.queryInputsAddressed, LeafHeadSetupProgram.Native.queryInputs,
      LeafHeadSetupProgram.unary] using hu 7
  · change BinaryArithmetic.toNat
      (a.stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high 13))) = _
    rw [hp 13 (by decide) (by decide) (by decide)]
    change BinaryArithmetic.toNat (front.stacks 141) = _
    rw [hf.offset]
    have ho : m.val 3 = (q.input k).occurrence := Execute.guardedModel_input _ _ 3
    change 2 * m.val 3 * (8 * m.val 21) ^ (2 * m.val 29) = _
    rw [ho, hQ, hR]
    rfl
  · exact hnode

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
