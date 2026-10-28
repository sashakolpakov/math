import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedRowSource
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedLayoutEnumeration
import OAI.Algorithms.SubexponentialSAT.SubexpSelectedSource
import OAI.Algorithms.SubexponentialSAT.SubexpLeafTables

namespace OAI.Algorithms

/-!
# Construct source counting data from the computed layout

Local tables, origins, rows, and Taylor input are generated here. The caller
supplies finite input orders and checked numerical construction bounds, not
local polynomial/table identities. The field-node representation is explicit;
the selected machine-node adapter discharges that input separately.
-/

namespace SubexponentialSAT.Subexp.ComputedSource

open SubexponentialSAT.MulticolorTypes ConstructivePacking ComputedLayout ComputedLayoutEnumeration
open SubexpSelectedConversions SubexpRowInterpolation SubexpTaylorExecution
open SubexpRepresentedRows SubexpLayoutSpec

theorem fin_size {D d : ℕ} (h : d ≤ D) : d ≤ Fintype.card (Fin D) := by
  simpa only [Fintype.card_fin] using h

variable {D p k Δ r : ℕ} {τ : ℚ} [Fact p.Prime] [NeZero r]
variable {F : Type*} [Fintype F] [DecidableEq F]
variable (S : Factor.System (Fin D) F (ZMod p))
variable (c : Parameters p k Δ r τ)
variable (hP : S.toPattern.Bounded k Δ) (hsize : c.Dstar ≤ D)
variable (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
  (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar)
variable (hE : Module.finrank (ZMod p) (SubexpActualRing.E p) = c.h)
variable (nodes : Fin c.Q ≃ {z : SubexpActualRing.E p // z ≠ 0})
variable (slots : SlotAssignment.SlotMap S.toPattern Δ)
variable (vertices : FiniteEnumeration (Fin D)) (types : FiniteEnumeration (UniversalType r c.Q Δ))
variable (indices : FiniteEnumeration (SubexpTypeVariance.SeedIndex (Fin D) F Δ))
variable (a : Word r c.Q) (tail : List (Word r c.Q))
variable (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
variable (A : ℕ) (htail : SpectralRank.normalizedTail r (c.Q - 1) A c.R ≤ τ / (Δ : ℚ))

local notation "L" => layoutWithWordsOfTail S.toPattern c hP
  (fin_size hsize) hthreshold hE nodes slots
  vertices types indices a tail haNodup haFull A htail

variable (source : Prepared p 0) (target : Prepared p D)
variable (nodeWords : Fin c.Q → SubexpSymbolicCost.QuarticCode p 0)
variable (hnodeWords : ∀ t, source.residueRing.decode (nodeWords t) = (nodes t).val)
variable (factors : FiniteEnumeration F)
variable (scopeLists : F → List (Fin D))
variable (scopeNodup : ∀ e, (scopeLists e).Nodup)
variable (scopeMem : ∀ e v, v ∈ scopeLists e ↔ v ∈ S.scope e)

/-- The emitted scope order becomes the coordinate order of its table. -/
def scopeIndex (e : F) : Fin (scopeLists e).length ≃ {v // v ∈ S.scope e} :=
  SubexpLeafTables.scopeOfList S e (scopeLists e) (scopeNodup e) (scopeMem e)

/-- All row polynomials are constructed using represented field arithmetic. -/
def fieldRow (e : F) (i : Fin (scopeLists e).length) (w : Fin D) :
    PolynomialCode (SubexpSymbolicCost.QuarticCode p 0) :=
  ComputedRowSource.rowCode S.toPattern c slots vertices types indices a tail A
    source.program (p ^ 4) nodeWords embedCode e
    (scopeIndex S scopeLists scopeNodup scopeMem e i) w

/-- Actual local factor data before Taylor preprocessing. -/
def factorSource (t : Fin c.Q) (e : F) :
    SubexpFactorCode.FactorSource D p r
      (SubexpSymbolicCost.QuarticCode p 0) (SubexpSymbolicCost.QuarticCode p D) where
  arity := (scopeLists e).length
  color := factorWordsWithWords S.toPattern slots vertices indices a tail e t
  origin i w := originValue source.program
    (fieldRow S c slots vertices types indices a tail A source nodeWords
      scopeLists scopeNodup scopeMem e i w) (nodeWords t)
  rows i w := liftCode source.program target.program (betaLift source D) c.R
    (fieldRow S c slots vertices types indices a tail A source nodeWords
      scopeLists scopeNodup scopeMem e i w)
  table := SubexpLeafTables.orderedRows S e
    (scopeIndex S scopeLists scopeNodup scopeMem e) target.zero target.one

include hP hsize hthreshold hE haNodup haFull htail hnodeWords in
theorem fieldRow_decode (e : F) (i : Fin (scopeLists e).length) (w : Fin D) :
    (mapCode source.residueRing.decode (fieldRow S c slots vertices types indices a tail A
      source nodeWords scopeLists scopeNodup scopeMem e i w)).denote =
      (L).row e (scopeIndex S scopeLists scopeNodup scopeMem e i) w := by
  exact ComputedRowSource.rowCode_decode S.toPattern c hP
    (by simpa only [Fintype.card_fin] using hsize) hthreshold hE nodes slots
    vertices types indices a tail haNodup haFull A htail source.residueRing (p ^ 4)
    (SubexpActualRing.extension_card p) nodeWords hnodeWords embedCode (embedCode_decode source)
    e (scopeIndex S scopeLists scopeNodup scopeMem e i) w

include hP hsize hthreshold hE haNodup haFull htail hnodeWords in
/-- Retaining `R + 1` source coefficients preserves the complete row before
the coefficientwise residue lift or a Taylor shift. -/
theorem fieldRow_degree (e : F) (i : Fin (scopeLists e).length) (w : Fin D) :
    (mapCode source.residueRing.decode (fieldRow S c slots vertices types indices a tail A
      source nodeWords scopeLists scopeNodup scopeMem e i w)).denote.natDegree ≤ c.R := by
  rw [fieldRow_decode S c hP hsize hthreshold hE nodes slots vertices types indices
    a tail haNodup haFull A htail source nodeWords hnodeWords scopeLists scopeNodup scopeMem]
  exact (L).row_degree e (scopeIndex S scopeLists scopeNodup scopeMem e i) w

variable (pairs : ∀ t : Fin c.Q, SidePairs p r c.Q Δ t)
variable (hpairs : ∀ (t : Fin c.Q) (g : Fin r),
  BlockSearch.GoodPair (LocalEnumeration.canonicalConstraintMatrix (Δ := Δ) t g c.R
    (CoefficientSearch.coefficientsNat p A c.R)) (pairs t g))

/-- Use exactly the locally checked pairs returned by the actual finite search.
Their enumeration order need not match a different mathematical search. -/
noncomputable def enumeration (t : Fin c.Q) : EnumerationData L t :=
  enumerationForPairs S.toPattern c hP (by simpa only [Fintype.card_fin] using hsize)
    hthreshold hE nodes slots vertices types indices a tail haNodup haFull A htail t
    (pairs t) (hpairs t)

/-- Membership is tested by the actual packing lookup, in ambient index order. -/
def supports (t : Fin c.Q) (g : Fin r) : List (Fin D) :=
  (List.finRange D).filter fun v =>
    supportAt (packingWithWords S.toPattern slots vertices types indices a tail)
      (MulticolorTypes.side (Δ := Δ) t g).toFinset v

include hP hsize hthreshold hE haNodup haFull htail in
theorem supports_eq : supports S c slots vertices types indices a tail =
    SubexpEnumerationCode.supportLists L := by
  funext t g
  apply List.filter_congr
  intro v _
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  exact layoutWithWords_supportAt S.toPattern c hP
    (by simpa only [Fintype.card_fin] using hsize) hthreshold hE nodes _ slots
    vertices types indices a tail haNodup haFull t g v

/-- This constructor discharges the local table, origin, and row obligations
from the computed algorithms. No desired count or polynomial is an input.
The record also contains the semantic layout/field interpretation, so this
proof-facing assembly is noncomputable; the raw row generators above are
separate from this annotation and from the physical producer. -/
noncomputable def input : SubexpCountSource.SourceInput S L source.residueRing target.ring where
  node t := betaLift source D (nodeWords t)
  node_decode t := by
    rw [betaLift_decode, hnodeWords]
    rfl
  enumeration := enumeration S c hP hsize hthreshold hE nodes slots vertices types indices
    a tail haNodup haFull A htail pairs hpairs
  supports := supports S c slots vertices types indices a tail
  supports_eq := supports_eq S c hP hsize hthreshold hE nodes slots vertices types indices
    a tail haNodup haFull A htail
  outside t := SubexpComputedWeights.outsideCoordinates
    (supports S c slots vertices types indices a tail t)
  outside_eq := by
    rw [supports_eq S c hP hsize hthreshold hE nodes slots vertices types indices
      a tail haNodup haFull A htail]
    rfl
  bases t := SubexpEnumerationCode.outerBases
    (enumeration S c hP hsize hthreshold hE nodes slots vertices types indices
      a tail haNodup haFull A htail pairs hpairs t)
  bases_eq := rfl
  increments t := SubexpEnumerationCode.innerIncrements
    (enumeration S c hP hsize hthreshold hE nodes slots vertices types indices
      a tail haNodup haFull A htail pairs hpairs t)
  increments_eq := rfl
  factors := factors.values
  factors_nodup := factors.nodup
  factors_complete := factors.complete
  source := factorSource S c slots vertices types indices a tail A source target nodeWords
    scopeLists scopeNodup scopeMem
  scopeIndex _ e := scopeIndex S scopeLists scopeNodup scopeMem e
  color_eq _ _ := rfl
  table_eq _ e := SubexpLeafTables.orderedRows_correct target.ring S e
    (scopeIndex S scopeLists scopeNodup scopeMem e)
  origin_eq t e i w := by
    let i' : Fin (scopeLists e).length := i
    dsimp only [factorSource]
    rw [← Prepared.residueRing_program source, originValue_decode source.residueRing]
    rw [fieldRow_decode S c hP hsize hthreshold hE nodes slots vertices types indices
      a tail haNodup haFull A htail source nodeWords hnodeWords scopeLists scopeNodup scopeMem e i',
      hnodeWords]
    rfl
  row_eq t e i w := by
    let i' : Fin (scopeLists e).length := i
    change (mapCode target.ring.decode
      (liftCode source.residueRing.program target.ring.program (betaLift source D) c.R
        (fieldRow S c slots vertices types indices a tail A source nodeWords scopeLists
          scopeNodup scopeMem e i' w))).denote = _
    rw [liftCode_decode source.residueRing target.ring (betaLift source D)
      (SubexpActualRing.sectionValue p (D + 1) (Nat.succ_pos D))
      (betaLift_decode source target)]
    rw [fieldRow_decode S c hP hsize hthreshold hE nodes slots vertices types indices
      a tail haNodup haFull A htail source nodeWords hnodeWords scopeLists scopeNodup scopeMem e i']
    rfl

/-- The represented counting reference computation with all local source
identities supplied by the concrete constructor above. The separate byte
program still has to implement this reference computation. -/
noncomputable def run : List (SubexpSymbolicCost.QuarticCode p D) × ℕ :=
  SubexpCountExecution.runSelected S L source.residueRing target.ring
    (SubexpSelectedSource.toSelectedInput S L source target
      (input S c hP hsize hthreshold hE nodes slots vertices types indices a tail
        haNodup haFull A htail source target nodeWords hnodeWords factors
        scopeLists scopeNodup scopeMem pairs hpairs))

/-- No local table, origin, or row-polynomial identity is a caller premise. -/
theorem run_decodeCount (hD : 0 < D) :
    SubexpActualRing.decodeCount p (D + 1) (Nat.succ_pos D)
      ((PolynomialAlgorithm.denote
        ((run S c hP hsize hthreshold hE nodes slots vertices types indices a tail
          haNodup haFull A htail source target nodeWords hnodeWords factors
          scopeLists scopeNodup scopeMem pairs hpairs).1.map target.ring.decode)).coeff 0) =
      Factor.count S :=
  SubexpSelectedSource.run_decodeCount S L source target
    (input S c hP hsize hthreshold hE nodes slots vertices types indices a tail
      haNodup haFull A htail source target nodeWords hnodeWords factors
      scopeLists scopeNodup scopeMem pairs hpairs) hD

end SubexponentialSAT.Subexp.ComputedSource

end OAI.Algorithms
