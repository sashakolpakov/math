import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConcreteSourceProvenance
import OAI.Algorithms.SubexponentialSAT.SubexpMainPhysicalLayoutFields

namespace OAI.Algorithms

/-! Changing a layout's pattern along the proved physical-system equality
does not change the node source specification or its ordered enumeration. -/

namespace SubexponentialSAT.SubexpNodeReferenceTransport

noncomputable section

open SubexpLayoutSpec SubexpSelectedConversions SubexpSymbolicCost
open SubexpMainPhysicalLayoutFields.PatternTransport

variable {p D k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F : Type*} [Fintype F] [DecidableEq F] {arity : F → ℕ}
  {P P' : Factor.Pattern (Fin D) F} {params : Parameters p k Δ r tau}
  (eqPattern : P = P') (L : Layout (E := SubexpActualRing.E p) P params)
  (node : Fin params.Q) (enum : EnumerationData L node)
  (ctx : SubexpMomentSourceProgram.Context) (hdimension : ctx.dimension = D)
  (source : Prepared p 0) (theta : QuarticCode p D)
  (packetInputs : ∀ e, SubexpFactorPacketProvenance.Input p D p (arity e) params.R)
  (es : List F) (words : F → MulticolorTypes.Word r params.Q)
  (cache : List (List (QuarticCode p D)))

theorem reference_eq (ctx : SubexpMomentSourceProgram.Context)
    {F : Type*} [Fintype F] [DecidableEq F] {arity : F → ℕ}
    {P P' : Factor.Pattern (Fin ctx.dimension) F}
    (eqPattern : P = P')
    (L : Layout (E := SubexpActualRing.E p) P params)
    (node : Fin params.Q) (enum : EnumerationData L node)
    (source : Prepared p 0) (theta : QuarticCode p ctx.dimension)
    (packetInputs : ∀ e, SubexpFactorPacketProvenance.Input p ctx.dimension p (arity e) params.R)
    (es : List F) (words : F → MulticolorTypes.Word r params.Q)
    (cache : List (List (QuarticCode p ctx.dimension))) :
    SubexpConcreteSourceProvenance.reference (ctx := ctx) (layout eqPattern L) node
      (enumeration eqPattern L node enum) source theta packetInputs es words cache =
    SubexpConcreteSourceProvenance.reference (ctx := ctx) L node enum source theta
      packetInputs es words cache := by
  cases eqPattern
  rfl

end

end SubexponentialSAT.SubexpNodeReferenceTransport

end OAI.Algorithms
