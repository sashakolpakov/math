import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWorkerExecution
import OAI.Algorithms.SubexponentialSAT.SubexpConcreteSourceProvenance
import OAI.Algorithms.SubexponentialSAT.Subexp.RawTemplateSupports
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheAlgebra

namespace OAI.Algorithms

/-! The worker's numeric packets and the source-provenance theorem use the
same raw blocks, context and typed template inputs. This adapter makes that
identity explicit and removes the worker's whole-input provenance premise
in favor of local source-degree and interpolation-cache facts. -/

namespace SubexponentialSAT.SubexpNodeWorkerProvenance

noncomputable section

open SubexpLayoutSpec SubexpNodeContexts SubexpNodeWorkspace
open SubexpSelectedConversions SubexpLiftRing SubexpQuarticRing SubexpSymbolicCost
open SubexpMomentSourceProgram SubexpMomentSourceSemantics MulticolorTypes

variable {p D k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  (masters : Store) (source : Prepared p 0) (target : Prepared p D)
  (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
  (hm : SubexpNodeContextSemantics.Masters masters source target minusOne)
  (theta : QuarticCode p D)
  (cache : List (List (QuarticCode p D)))
  (expr : ℕ → ℕ → ℕ → SubexpTaylorRowCorrectness.RowExpr p)
  (scopes : List (List ℕ)) (tables : List (List Bool))
  {pattern : Factor.Pattern (Fin D) (Fin scopes.length)}
  {params : Parameters p k Δ r tau}
  (L : Layout (E := SubexpActualRing.E p) pattern params)
  (node : Fin params.Q) (enum : EnumerationData L node)
  (packing : Subexp.ConstructivePacking.PackingData (Fin D) (UniversalType r params.Q Δ))
  (words : Fin scopes.length → MulticolorTypes.Word r params.Q)

local notation "factor" => SubexpNodePacketInputs.factor source target theta params.R (masters 129)
  hm.sourceWidth cache target.zero target.one expr scopes tables
local notation "order" => List.finRange scopes.length
local notation "packet" => SubexpNodePacketRaw.packet source target theta factor
local notation "rawBlocks" => Subexp.RawTemplateRefinement.blocks packing node order words packet
  (SubexpEnumerationCode.outerBases enum) (SubexpEnumerationCode.innerIncrements enum)
local notation "rawGood" => Subexp.RawTemplateRefinement.blocks_good packing node order words packet
  (SubexpEnumerationCode.outerBases enum) (SubexpEnumerationCode.innerIncrements enum)
local notation "TC" => templateContext masters D
local notation "templateBytes" => SubexpTemplateExecution.output TC source target minusOne rawBlocks
local notation "Ctx" => sourceContext masters D templateBytes
local notation "coefficients" => QuarticSearch.liftedCoefficients p (D+1)

def reference (a : Fin D → ℕ) :=
  SubexpConcreteSourceProvenance.reference (ctx := Ctx) L node enum source theta
    (fun e => (factor e).data) order words cache a

theorem provenance
    (hsupport : Subexp.RawTemplateRefinement.colorSupport packing node =
      SubexpEnumerationCode.supportLists L node)
    (houtside : Subexp.RawTemplateRefinement.outsideSupport packing =
      SubexpEnumerationCode.outsideList L node)
    (hminusOne : wordValue p (D+1) minusOne = -1)
    (hdegree : ∀ (e : Fin scopes.length) (i : Fin (scopes.get e).length) (w : Fin D),
      (((expr e.val ((scopes.get e).get i) w.val).map
        (SubexpRowSourceSemantics.denote source)).eval).natDegree ≤ params.R)
    (hcache : ∀ i : Fin p,
      PolynomialAlgorithm.denote
        ((cache.map (List.map (SubexpFactorPacketProvenance.decode p D))).getD i.val []) =
      TableInterpolation.basis (SubexpLagrangeCacheAlgebra.integerNodes p (D+1))
        (SubexpLagrangeCacheAlgebra.integerNodes_units p (D+1)) i) :
    letI : One (QuarticCode p D) := ⟨target.one⟩
    letI : One (QuarticCode p (Ctx).dimension) := ⟨target.one⟩
    ∀ a : Fin D → ℕ,
      letI : One (QuarticCode p ((Ctx).withExponent (SubexpExponentController.momentWord a)).dimension) :=
        ⟨target.one⟩
      List.Forall₂
        (SubexpProducedSourceRefinement.BlockProvenance
          (ctx := (Ctx).withExponent (SubexpExponentController.momentWord a)) coefficients a)
        ((SubexpNodeTemplateMoment.inputs masters source target minusOne hm rawBlocks rawGood).map
          (fun b => b.withExponent (SubexpExponentController.momentWord a)))
        (reference masters source target minusOne hm theta cache expr scopes tables L node enum
          packing words a) := by
  let : One (QuarticCode p D) := ⟨target.one⟩
  let : One (QuarticCode p (Ctx).dimension) := ⟨target.one⟩
  intro a
  let : One (QuarticCode p ((Ctx).withExponent (SubexpExponentController.momentWord a)).dimension) :=
    ⟨target.one⟩
  have h := SubexpConcreteSourceProvenance.provenance (ctx := Ctx)
    L node packing enum source target theta (fun e => (factor e).data) order words minusOne TC
    hm.sourceWidth rfl rfl hsupport houtside hminusOne (fun e _ => hdegree e) cache
    (fun _ _ => rfl) (SubexpLagrangeCacheAlgebra.integerNodes p (D+1))
    (SubexpLagrangeCacheAlgebra.integerNodes_units p (D+1)) hcache a
  exact h

end

end SubexponentialSAT.SubexpNodeWorkerProvenance

end OAI.Algorithms
