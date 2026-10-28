import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeMomentOrder
import OAI.Algorithms.SubexponentialSAT.SubexpNodeJetSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpCRTSelectedInput
import OAI.Algorithms.SubexponentialSAT.SubexpCountExecution

namespace OAI.Algorithms

/-! Exact CRT representations of the node collector's output words.
The node coefficients follow the physical tuple/filter order. A jet is
the actual list of cells returned by the moment phase, with its proved
length; neither operation changes or reorders the stored bytes. -/

namespace SubexponentialSAT.SubexpMainMomentReadback

noncomputable section

open SubexpQuarticRing SubexpLiftRing SubexpSymbolicCost

variable (p D : ℕ) [Fact p.Prime]

def nodeCode (i : Fin (p^4 - 1)) : SubexpCRTSelectedInput.Coefficient p D :=
  (SubexpFieldNodes.liftQuad p (D + 1)
    (SubexpMachineNodeOrder.nodeCoefficients p i)).map (encodeWord p (D + 1))

theorem nodeCode_decode (i : Fin (p^4 - 1)) :
    SubexpCRTSelectedInput.decode p D (nodeCode p D i) =
      SubexpActualRing.sectionValue p (D + 1) (Nat.succ_pos D)
        (SubexpMachineNodeOrder.nodeEquiv p i).val := by
  unfold SubexpCRTSelectedInput.decode nodeCode
  simp only [Quad.map, wordValue_encodeWord]
  exact SubexpMachineNodeOrder.lifted_node_value p (D + 1) (Nat.succ_pos D) i

theorem nodeCode_word (i : Fin (p^4 - 1)) :
    SubexpFlatAdd.encode (nodeCode p D i) =
      SubexpNodeMomentOrder.nodeWord p (D + 1) (Nat.succ_pos D) i := by
  have h := SubexpMachineNodeOrder.lifted_node_code p (D + 1) (Nat.succ_pos D) i
  simpa only [nodeCode, SubexpFlatAdd.encode, SubexpFlatAdd.quadWords,
    SubexpFlatAdd.flatten, Quad.map, encodeWord, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil,
    SubexpQuarticEncoding.encodeQuad, SubexpNodeMomentOrder.nodeWord, List.append_assoc] using h

theorem node_words :
    (List.ofFn (SubexpNodeMomentOrder.nodeWord p (D + 1) (Nat.succ_pos D))).flatten =
      (List.finRange (p^4 - 1)).flatMap (fun i => SubexpFlatAdd.encode (nodeCode p D i)) := by
  simp only [nodeCode_word, List.flatMap_def, ← List.ofFn_eq_map]

def jetOfCells (cells : List (QuarticCode p D)) (hlen : cells.length = D) :
    SubexpCRTSelectedInput.Jet p D := ⟨cells, hlen⟩

omit [Fact p.Prime] in
theorem jetOfCells_word (cells : List (QuarticCode p D)) (hlen : cells.length = D) :
    SubexpPolynomialPowerProgram.encode p (D + 1) (jetOfCells p D cells hlen) =
      SubexpMomentPhase.cellsBytes p D cells := rfl

theorem jetOfCells_decode (cells : List (QuarticCode p D)) (hlen : cells.length = D) :
    SubexpCRTSelectedInput.denote p D (jetOfCells p D cells hlen) =
      PolynomialAlgorithm.denote (cells.map (SubexpCRTSelectedInput.decode p D)) := rfl

theorem jetOfCells_decode_jet (cells : List (QuarticCode p D)) (hlen : cells.length = D)
    (theta : SubexpActualRing.Ring p (D + 1))
    (poly : Polynomial (SubexpActualRing.Ring p (D + 1)))
    (hcells : cells.map (SubexpCRTSelectedInput.decode p D) =
      (List.range D).map (JetCRT.jet theta D poly).coeff) :
    SubexpCRTSelectedInput.denote p D (jetOfCells p D cells hlen) =
      JetCRT.jet theta D poly := by
  rw [jetOfCells_decode, hcells]
  exact SubexpCountExecution.denote_jetCoefficientList D theta poly

omit [Fact p.Prime] in
theorem jet_words {Q : ℕ} (cells : Fin Q → List (QuarticCode p D))
    (hlen : ∀ i, (cells i).length = D) :
    (List.ofFn (fun i => SubexpMomentPhase.cellsBytes p D (cells i))).flatten =
      (List.finRange Q).flatMap (fun i =>
        SubexpPolynomialPowerProgram.encode p (D + 1) (jetOfCells p D (cells i) (hlen i))) := by
  simp only [jetOfCells_word, List.flatMap_def, ← List.ofFn_eq_map]

def jetOfFamily (ctx : SubexpMomentSourceProgram.Context)
    (target : SubexpSelectedConversions.Prepared p ctx.dimension)
    (actual : SubexpNodeJetSemantics.Family p ctx.dimension) :
    SubexpCRTSelectedInput.Jet p ctx.dimension :=
  jetOfCells p ctx.dimension (SubexpNodeJetSemantics.cells ctx target actual)
    (SubexpNodeJetSemantics.cells_length ctx target actual)

theorem jetOfFamily_word (ctx : SubexpMomentSourceProgram.Context)
    (target : SubexpSelectedConversions.Prepared p ctx.dimension)
    (actual : SubexpNodeJetSemantics.Family p ctx.dimension) :
    letI : One (QuarticCode p ctx.dimension) := ⟨target.one⟩
    SubexpPolynomialPowerProgram.encode p (ctx.dimension + 1) (jetOfFamily p ctx target actual) =
      SubexpNodePhaseExecution.jet p ctx.dimension target.modulus target.reduction
        target.zero target.one (SubexpQueryOrder.visitSlots ctx.dimension)
        (SubexpNodeSourceJobs.expression p ctx actual)
        (SubexpQueryOrder.generatedQueries ctx.dimension) := rfl

section Selected

variable {p} {k Δ r : ℕ} {tau : ℚ}
  {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  (S : Factor.System V F (ZMod p))
  {c : SubexpLayoutSpec.Parameters p k Δ r tau}
  (L : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p) S.toPattern c)

local notation "N" => Fintype.card V

omit [DecidableEq F] in
theorem selectedNode_section (i : Fin c.Q) :
    SubexpCRTAtZero.selectedNode S L i =
      SubexpActualRing.sectionValue p (N + 1) (Nat.succ_pos N) (L.node i) := rfl

omit [DecidableEq F] in
theorem nodeCode_selected (i : Fin c.Q) (j : Fin (p^4 - 1))
    (hnode : L.node i = (SubexpMachineNodeOrder.nodeEquiv p j).val) :
    SubexpCRTSelectedInput.decode p N (nodeCode p N j) =
      SubexpCRTAtZero.selectedNode S L i := by
  rw [nodeCode_decode, selectedNode_section, hnode]

def selectedPolynomial : Polynomial (SubexpActualRing.Ring p (N + 1)) :=
  GlobalPolynomial.rowGlobalPolynomial
    (GlobalPolynomial.interpolatedTable S (SubexpActualRing.coordinateLift p (N + 1))
      (SubexpActualRing.coordinateLift_unitDifferences p (N + 1)))
    (SubexpExplicitLift.explicitLiftedLayout L (N + 1) (Nat.succ_pos N)).row
    (SubexpActualRing.coordinateLift p (N + 1))

omit [DecidableEq F] in
theorem selectedJet_eq (i : Fin c.Q) :
    SubexpCRTSelectedInput.selectedJet S L i =
      JetCRT.jet (SubexpCRTAtZero.selectedNode S L i) N (selectedPolynomial S L) := by
  exact SubexpCounting.layoutJet_eq
    (SubexpExplicitLift.explicitLiftedLayout L (N + 1) (Nat.succ_pos N))
    (SubexpActualRing.coordinateLift p (N + 1))
    (SubexpActualRing.rho_coordinateLift p (N + 1) (Nat.succ_pos N))
    (SubexpActualRing.residueSection p (N + 1) (Nat.succ_pos N))
    (GlobalPolynomial.interpolatedTable S (SubexpActualRing.coordinateLift p (N + 1))
      (SubexpActualRing.coordinateLift_unitDifferences p (N + 1)))
    (N + 1) N (SubexpActualRing.prime_power_zero p (N + 1))
    (SubexpActualRing.rho_ker p (N + 1) (Nat.succ_pos N)) i

omit [DecidableEq F] in
theorem jetOfCells_selected (i : Fin c.Q)
    (cells : List (QuarticCode p N)) (hlen : cells.length = N)
    (hcells : cells.map (SubexpCRTSelectedInput.decode p N) =
      (List.range N).map
        (JetCRT.jet (SubexpCRTAtZero.selectedNode S L i) N (selectedPolynomial S L)).coeff) :
    SubexpCRTSelectedInput.denote p N (jetOfCells p N cells hlen) =
      SubexpCRTSelectedInput.selectedJet S L i :=
  (jetOfCells_decode_jet p N cells hlen _ _ hcells).trans (selectedJet_eq S L i).symm

end Selected

end
end SubexponentialSAT.SubexpMainMomentReadback

end OAI.Algorithms
