import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodePreparedMoment
import OAI.Algorithms.SubexponentialSAT.SubexpConcreteSourceProvenance
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheAlgebra

namespace OAI.Algorithms

/-! Interpretation of the actual node moment output. The returned source
family is related to the concrete packet reference by the source producer.
Local row, origin and table facts identify its decoded cells with the jet
of the same layout, using the explicit coefficientwise ring lift. -/

namespace SubexponentialSAT.SubexpNodeJetSemantics

noncomputable section

open SubexpMomentSourceProgram SubexpSelectedConversions SubexpLayoutSpec
open SubexpQuarticRing SubexpLiftRing SubexpSymbolicCost

abbrev Family (p D : ℕ) :=
  (Fin D → ℕ) → List (SubexpBlockAssemblySemantics.Block (QuarticCode p D)
    (SymbolicCost.CoeffList D (QuarticCode p D)))

variable {p : ℕ} [Fact p.Prime] (ctx : Context)
  (target : Prepared p ctx.dimension) (actual : Family p ctx.dimension)

def cells : List (QuarticCode p ctx.dimension) :=
  letI : One (QuarticCode p ctx.dimension) := ⟨target.one⟩
  (SubexpQueryOrder.generatedQueries ctx.dimension).foldl
    (SubexpMomentPhase.step p ctx.dimension target.modulus target.reduction target.zero target.one
      (SubexpQueryOrder.visitSlots ctx.dimension) (SubexpNodeSourceJobs.expression p ctx actual))
    (SubexpMomentPhase.zeroCells p ctx.dimension)

theorem cells_length : (cells ctx target actual).length = ctx.dimension := by
  unfold cells
  rw [SubexpMomentPhase.fold_length, SubexpMomentPhase.zeroCells_length]

theorem jet_eq_cellsBytes :
    letI : One (QuarticCode p ctx.dimension) := ⟨target.one⟩
    SubexpNodePhaseExecution.jet p ctx.dimension target.modulus target.reduction target.zero target.one
      (SubexpQueryOrder.visitSlots ctx.dimension) (SubexpNodeSourceJobs.expression p ctx actual)
      (SubexpQueryOrder.generatedQueries ctx.dimension) =
      SubexpMomentPhase.cellsBytes p ctx.dimension (cells ctx target actual) := rfl

variable {k Δ r : ℕ} {tau : ℚ} {F : Type*} [Fintype F] [DecidableEq F]
  {arity : F → ℕ} {pattern : Factor.Pattern (Fin ctx.dimension) F}
  {params : Parameters p k Δ r tau}
  (L : Layout (E := SubexpActualRing.E p) pattern params)
  (node : Fin params.Q) (enum : EnumerationData L node)
  (source : Prepared p 0) (theta : QuarticCode p ctx.dimension)
  (packetInputs : ∀ e, SubexpFactorPacketProvenance.Input p ctx.dimension p (arity e) params.R)
  (es : List F) (words : F → MulticolorTypes.Word r params.Q)
  (cache : List (List (QuarticCode p ctx.dimension)))

local notation "D" => ctx.dimension
local notation "C" => QuarticCode p ctx.dimension
local notation "coefficients" => QuarticSearch.liftedCoefficients p (ctx.dimension + 1)
local notation "decode" => SubexpFactorPacketProvenance.decode p ctx.dimension
local notation "A" => SubexpExplicitLift.explicitLiftedLayout L (ctx.dimension + 1) (Nat.succ_pos ctx.dimension)
local notation "coordinate" => SubexpActualRing.coordinateLift p (ctx.dimension + 1)
local notation "labels" => SubexpLagrangeCacheAlgebra.integerNodes p (ctx.dimension + 1)
local notation "labelUnits" => SubexpLagrangeCacheAlgebra.integerNodes_units p (ctx.dimension + 1)

/-- The finite rows and the executed source-family relation suffice to
interpret the stored cells. Taylor identities, arithmetic correctness,
nilpotence and the residue kernel are discharged inside this proof. -/
theorem cells_eq_layoutJet
    (hnodup : es.Nodup) (hcomplete : ∀ e, e ∈ es)
    (ix : ∀ e, Fin (arity e) ≃ {v // v ∈ pattern.scope e})
    (table : ∀ e, MvPolynomial {v // v ∈ pattern.scope e}
      (SubexpActualRing.Ring p (ctx.dimension + 1)))
    (hcolor : ∀ e, words e node = L.color e node)
    (htable : ∀ e, SubexpTableInterpolation.tablePolynomial labels labelUnits
      ((packetInputs e).rows.map (SubexpRepresentedBuilder.mapRow decode)) =
        MvPolynomial.rename (ix e).symm (table e))
    (horigin : ∀ e i w, source.residueRing.decode ((packetInputs e).origins i w) =
      (L.row e (ix e i) w).eval (L.node node))
    (hrow : ∀ e i w,
      (((packetInputs e).sourceRows i w).map (SubexpRowSourceSemantics.denote source)).eval =
        L.row e (ix e i) w)
    (htheta : decode theta = (A).theta node)
    (hcache : ∀ i : Fin p,
      PolynomialAlgorithm.denote ((cache.map (List.map decode)).getD i.val []) =
        TableInterpolation.basis labels labelUnits i)
    (hrel : letI : One C := ⟨target.one⟩
      ∀ a : Fin D → ℕ,
        List.Forall₂ (SubexpSourceReference.BlockRel decode) (actual a)
          (SubexpConcreteSourceProvenance.reference (ctx := ctx)
            L node enum source theta packetInputs es words cache a)) :
    (cells ctx target actual).map decode = (List.range D).map fun j =>
      (JetCRT.jet ((A).theta node) D
        (GlobalPolynomial.rowGlobalPolynomial table (A).row coordinate)).coeff j := by
  let this : One C := ⟨target.one⟩
  let data := fun e => SubexpFactorPacketProvenance.referenceData source theta
    (packetInputs e) (words e node)
  have hrows (e : F) (i : Fin (arity e)) (w : Fin D) :
      SubexpFactorPacketProvenance.liftedRow source (packetInputs e) i w = (A).row e (ix e i) w := by
    unfold SubexpFactorPacketProvenance.liftedRow
    rw [hrow]
    rfl
  have htaylor : ∀ e i j w, (data e).taylor i j w =
      (((A).row e (ix e i) w).comp (Polynomial.X + Polynomial.C ((A).theta node))).coeff j.val := by
    intro e i j w
    let i' : Fin (arity e) := Fin.cast (by rfl) i
    have hi : i' = i := Fin.ext rfl
    change ((SubexpFactorPacketProvenance.liftedRow source (packetInputs e) i' w).comp
      (Polynomial.X + Polynomial.C (decode theta))).coeff j.val = _
    rw [hrows e i' w, htheta, hi]
  have hlocal : ∀ a ∈ Algorithm.exponentList D (2 * D + 1),
      List.Forall₂ (SubexpSourceReference.BlockRel decode) (actual a)
        (SubexpSourceReference.blocks (algebraMap (ZMod p) (SubexpActualRing.E p))
          (SubexpActualRing.residueSection p (D + 1) (Nat.succ_pos D)).lift coordinate
          (cache.map (List.map decode)) (es.map data)
          (SubexpEnumerationCode.supportLists L node) (SubexpEnumerationCode.outsideList L node)
          (SubexpEnumerationCode.outerBases enum) (SubexpEnumerationCode.innerIncrements enum) a) := by
    intro a _
    exact hrel a
  have hj := SubexpSourceReference.jet_eq_layoutJet decode target.one_spec actual
    A coordinate (SubexpActualRing.rho_coordinateLift p (D + 1) (Nat.succ_pos D))
    (SubexpActualRing.residueSection p (D + 1) (Nat.succ_pos D)) node enum
    (cache.map (List.map decode)) labels labelUnits hcache es hnodup hcomplete data ix table
    hcolor htable horigin htaylor (SubexpActualRing.prime_power_zero p (D + 1))
    (SubexpActualRing.rho_ker p (D + 1) (Nat.succ_pos D)) hlocal
  have hc := SubexpMomentSemantics.generated_visitSlots_eq_rawJet p D target.modulus
    coefficients target.reduction target.zero target.one target.reduction_spec
    target.zero_spec target.one_spec (SubexpNodeSourceJobs.expression p ctx actual)
  exact hc.trans hj

end

end SubexponentialSAT.SubexpNodeJetSemantics

end OAI.Algorithms
