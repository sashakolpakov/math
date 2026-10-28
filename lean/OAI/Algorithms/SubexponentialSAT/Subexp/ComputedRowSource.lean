import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRepresentedRows
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedLayoutChoices

namespace OAI.Algorithms

/-!
# Represented rows for the layout with actual runtime choices

The code generator uses the finite matrix recurrence and the same packing
lookup as the constructed layout. Its inputs are represented nodes and
prime-field coefficients. No polynomial coefficient is read from a semantic
field element.
-/

namespace SubexponentialSAT.Subexp.ComputedRowSource

open SubexponentialSAT.MulticolorTypes ConstructivePacking SubexpSymbolicCost
open SubexpRowInterpolation SubexpTaylorExecution SubexpRepresentedRows

variable {C E V U I : Type*} [DecidableEq V] [DecidableEq U]

/-- Two packing lookups choose the local row or an explicit constant. -/
def lookupCode (zero one : C) (P : PackingData V U)
    (localRow : U → I → U → PolynomialCode C) (i : I) (v w : V) : PolynomialCode C :=
  match P.lookup v with
  | none => .constant (if w = v then one else zero)
  | some (j, u) =>
      match P.lookup w with
      | none => .constant zero
      | some (k, y) => if j = k then localRow u i y else .constant zero

section DecodeLookup

variable [Field E] (ops : RepresentedRing C E)

theorem lookupCode_decode (P : PackingData V U)
    (localRow : U → I → U → PolynomialCode C) (i : I) (v w : V) :
    (mapCode ops.decode (lookupCode ops.zeroRun.1 ops.oneRun.1 P localRow i v w)).denote =
      ComputedLayout.rowValue P (fun u i y => (mapCode ops.decode (localRow u i y)).denote) i v w := by
  cases hv : P.lookup v with
  | none =>
      by_cases h : w = v <;>
        simp [lookupCode, ComputedLayout.rowValue, hv, h, mapCode,
          PolynomialCode.denote, ops.zero_correct, ops.one_correct]
  | some a =>
      rcases a with ⟨j, u⟩
      cases hw : P.lookup w with
      | none => simp [lookupCode, ComputedLayout.rowValue, hv, hw, mapCode,
          PolynomialCode.denote, ops.zero_correct]
      | some b =>
          rcases b with ⟨k, y⟩
          by_cases h : j = k <;>
            simp [lookupCode, ComputedLayout.rowValue, hv, hw, h, mapCode,
              PolynomialCode.denote, ops.zero_correct]

end DecodeLookup

section MatrixCode

variable {p r Q Δ : ℕ} [Fact p.Prime]

def universalCode (ops : RingProgram C) (cache : NodeCache C Q)
    (embed : ZMod p → C) (R : ℕ) (coeff : ℕ → ZMod p)
    (u : UniversalType r Q Δ) (i : Fin Δ) (y : UniversalType r Q Δ) : PolynomialCode C :=
  matrixRow ops cache embed
    (fun t g i => ElementaryMatrix.jointMatrixDP i t g R coeff) u i R y

def globalCode (ops : RingProgram C) (cache : NodeCache C Q)
    (embed : ZMod p → C) (R : ℕ) (coeff : ℕ → ZMod p)
    (P : PackingData V (UniversalType r Q Δ)) (i : Fin Δ) (v w : V) : PolynomialCode C :=
  lookupCode ops.zeroRun.1 ops.oneRun.1 P (universalCode ops cache embed R coeff) i v w

variable [Field E] [Algebra (ZMod p) E]
variable (ops : RepresentedRing C E) (cache : NodeCache C Q)
variable {node : Fin Q → E} (units : NodeUnits node)
variable (hnode : ∀ i, ops.decode (cache.node i) = node i)
variable (hinv : ∀ i, ops.decode (cache.inverse i) = units.nodeInverse i)
variable (hdiff : ∀ i j, ops.decode (cache.difference i j) = units.differenceInverse i j)
variable (embed : ZMod p → C)
variable (hembed : ∀ a, ops.decode (embed a) = algebraMap (ZMod p) E a)

include hnode hinv hdiff hembed in
theorem universalCode_decode (R : ℕ) (coeff : ℕ → ZMod p)
    (u : UniversalType r Q Δ) (i : Fin Δ) (y : UniversalType r Q Δ) :
    (mapCode ops.decode (universalCode ops.program cache embed R coeff u i y)).denote =
      SubexpAnnihilation.universalRow (algebraMap (ZMod p) E) u i R coeff units y := by
  unfold universalCode
  rw [matrixRow_decode ops cache units hnode hinv hdiff embed (algebraMap (ZMod p) E) hembed]
  have hM : (fun (t : Fin Q) (g : Fin r) (i : Fin Δ) =>
      ElementaryMatrix.jointMatrixDP i t g R coeff) =
      (fun (t : Fin Q) (g : Fin r) (i : Fin Δ) =>
        MatrixSupport.jointMatrix i t g R coeff) := by
    funext t g i
    exact ElementaryMatrix.jointMatrixDP_eq i t g R coeff
  rw [hM]
  rfl

include hnode hinv hdiff hembed in
theorem globalCode_decode (R : ℕ) (coeff : ℕ → ZMod p)
    (P : PackingData V (UniversalType r Q Δ)) (i : Fin Δ) (v w : V) :
    (mapCode ops.decode (globalCode ops.program cache embed R coeff P i v w)).denote =
      _root_.OAI.Algorithms.SubexponentialSAT.Layout.assembledRow P.completeBlocks.embed
        (fun u i => SubexpAnnihilation.universalRow (algebraMap (ZMod p) E) u i R coeff units)
        i v w := by
  unfold globalCode
  rw [show ops.program.zeroRun.1 = ops.zeroRun.1 from rfl,
    show ops.program.oneRun.1 = ops.oneRun.1 from rfl, lookupCode_decode ops]
  simp_rw [universalCode_decode ops cache units hnode hinv hdiff embed hembed]
  exact ComputedLayout.rowValue_polynomial_eq _ _ _ _ _

end MatrixCode

section InverseCache

variable {Q : ℕ} [Field E] [Fintype E]
variable (ops : RepresentedRing C E) (q : ℕ) (hq : Fintype.card E = q)
variable (words : Fin Q → C) (node : Fin Q → E)
variable (hnode : ∀ i, ops.decode (words i) = node i)
variable (hinj : Function.Injective node) (hne : ∀ i, node i ≠ 0)

include hq hnode hne in
theorem cache_inverse (units : NodeUnits node) (i : Fin Q) :
    ops.decode ((nodeCache ops.program q words).inverse i) = units.nodeInverse i := by
  have he : (fun i => ops.decode (words i)) = node := funext hnode
  subst node
  exact nodeCache_inverse ops q hq words hne units i

include hq hnode hinj in
theorem cache_difference (units : NodeUnits node) (i j : Fin Q) :
    ops.decode ((nodeCache ops.program q words).difference i j) = units.differenceInverse i j := by
  have he : (fun i => ops.decode (words i)) = node := funext hnode
  subst node
  exact nodeCache_difference ops q hq words hinj units i j

end InverseCache

section ConstructedLayout

open ComputedLayout

variable {p k Δ r : ℕ} {τ : ℚ} [Fact p.Prime] [NeZero r]
variable {F : Type*} [Fintype V] [Fintype F] [DecidableEq F]
variable [Field E] [Fintype E] [Algebra (ZMod p) E]
variable (P : Factor.Pattern V F) (c : SubexpLayoutSpec.Parameters p k Δ r τ)
variable (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card V)
variable (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
  (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar)
variable (hE : Module.finrank (ZMod p) E = c.h)
variable (nodes : Fin c.Q ≃ {z : E // z ≠ 0})
variable (slots : SlotAssignment.SlotMap P Δ)
variable (vertices : FiniteEnumeration V) (types : FiniteEnumeration (UniversalType r c.Q Δ))
variable (indices : FiniteEnumeration (SubexpTypeVariance.SeedIndex V F Δ))
variable (a : Word r c.Q) (tail : List (Word r c.Q))
variable (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
variable (A : ℕ) (htail : SpectralRank.normalizedTail r (c.Q - 1) A c.R ≤ τ / (Δ : ℚ))

/-- Full represented row data, built from the actual computed packing. -/
def rowCode (ops : RingProgram C) (q : ℕ) (words : Fin c.Q → C)
    (embed : ZMod p → C) (e : F) (v : {v // v ∈ P.scope e}) (w : V) : PolynomialCode C :=
  globalCode ops (nodeCache ops q words) embed c.R (CoefficientSearch.coefficientsNat p A c.R)
    (packingWithWords P slots vertices types indices a tail)
    (slots v.val ⟨e, v.property⟩) v.val w

include hP hsize hthreshold hE haNodup haFull htail in
theorem rowCode_decode (ops : RepresentedRing C E) (q : ℕ) (hq : Fintype.card E = q)
    (words : Fin c.Q → C) (hwords : ∀ i, ops.decode (words i) = (nodes i).val)
    (embed : ZMod p → C) (hembed : ∀ z, ops.decode (embed z) = algebraMap (ZMod p) E z)
    (e : F) (v : {v // v ∈ P.scope e}) (w : V) :
    (mapCode ops.decode (rowCode P c slots vertices types indices a tail A
      ops.program q words embed e v w)).denote =
      (layoutWithWordsOfTail P c hP hsize hthreshold hE nodes slots
        vertices types indices a tail haNodup haFull A htail).row e v w := by
  let units := unitsForNodes nodes
  have hn : ∀ i, ops.decode ((nodeCache ops.program q words).node i) = (nodes i).val := hwords
  have hi : ∀ i, ops.decode ((nodeCache ops.program q words).inverse i) = units.nodeInverse i :=
    cache_inverse ops q hq words _ hwords (fun i => (nodes i).property) units
  have hd : ∀ i j, ops.decode ((nodeCache ops.program q words).difference i j) =
      units.differenceInverse i j :=
    cache_difference ops q hq words _ hwords (Subtype.val_injective.comp nodes.injective) units
  unfold rowCode
  rw [globalCode_decode ops _ units hn hi hd embed hembed]
  rfl

end ConstructedLayout

end SubexponentialSAT.Subexp.ComputedRowSource

end OAI.Algorithms
