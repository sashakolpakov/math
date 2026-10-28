import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedSource
import OAI.Algorithms.SubexponentialSAT.Subexp.RepresentedNodeOrder

namespace OAI.Algorithms

/-!
# Source data using the machine's actual quartic node order

The quartic degree fixes the number of nonzero nodes. The node-code decoder
identity is discharged by the actual tuple/filter order, rather than supplied
as a caller hypothesis. Local basis pairs, scopes, and assignment alphabets
retain their concrete runtime orders.

This is a representation and source-data constructor. The physical setup,
matrix, row, and enumeration producers carry their own execution theorems.
-/

namespace SubexponentialSAT.Subexp.ComputedMachineSource

open SubexponentialSAT.MulticolorTypes ConstructivePacking ComputedLayout ComputedLayoutEnumeration
open SubexpSelectedConversions SubexpLayoutSpec RepresentedNodeOrder

variable {D p k Δ r : ℕ} {τ : ℚ} [Fact p.Prime] [NeZero r]

private theorem fin_size {d D : ℕ} (h : d ≤ D) : d ≤ Fintype.card (Fin D) := by
  simpa only [Fintype.card_fin] using h

omit [Fact p.Prime] [NeZero r] in
theorem nodeCount_eq (c : Parameters p k Δ r τ) (h4 : c.h = 4) :
    c.Q = p ^ 4 - 1 := by
  rw [c.Q_eq, h4]

omit [NeZero r] in
theorem extension_degree (c : Parameters p k Δ r τ) (h4 : c.h = 4) :
    Module.finrank (ZMod p) (SubexpActualRing.E p) = c.h :=
  (SubexpActualRing.extension_finrank p).trans h4.symm

variable {F : Type*} [Fintype F] [DecidableEq F]
variable (S : Factor.System (Fin D) F (ZMod p))
variable (c : Parameters p k Δ r τ) (h4 : c.h = 4)
variable (hP : S.toPattern.Bounded k Δ) (hsize : c.Dstar ≤ D)
variable (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
  (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar)
variable (slots : SlotAssignment.SlotMap S.toPattern Δ)
variable (vertices : FiniteEnumeration (Fin D))
variable (types : FiniteEnumeration (UniversalType r c.Q Δ))
variable (indices : FiniteEnumeration (SubexpTypeVariance.SeedIndex (Fin D) F Δ))
variable (a : Word r c.Q) (tail : List (Word r c.Q))
variable (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
variable (A : ℕ) (htail : SpectralRank.normalizedTail r (c.Q - 1) A c.R ≤ τ / (Δ : ℚ))

local notation "L" => layoutWithWordsOfTail S.toPattern c hP
  (fin_size hsize) hthreshold (extension_degree c h4)
  (nodesFor p (nodeCount_eq c h4)) slots vertices types indices a tail haNodup haFull A htail

variable (source : Prepared p 0) (target : Prepared p D)
variable (factors : FiniteEnumeration F)
variable (scopeLists : F → List (Fin D))
variable (scopeNodup : ∀ e, (scopeLists e).Nodup)
variable (scopeMem : ∀ e v, v ∈ scopeLists e ↔ v ∈ S.scope e)
variable (pairs : ∀ t : Fin c.Q, SidePairs p r c.Q Δ t)
variable (hpairs : ∀ (t : Fin c.Q) (g : Fin r),
  BlockSearch.GoodPair
    (LocalEnumeration.canonicalConstraintMatrix (Δ := Δ) t g c.R
      (CoefficientSearch.coefficientsNat p A c.R)) (pairs t g))

/-- All node representation identities are proved for the actual machine
order. The remaining inputs are concrete construction data and numerical
feasibility conditions, not desired row or counting identities.
Proof-facing packaging retains the semantic field/layout dictionaries.
The represented row/node data and their byte producers remain separate. -/
noncomputable def input : SubexpCountSource.SourceInput S L source.residueRing target.ring :=
  ComputedSource.input S c hP hsize hthreshold (extension_degree c h4)
    (nodesFor p (nodeCount_eq c h4)) slots vertices types indices a tail
    haNodup haFull A htail source target (nodeCodeFor p (nodeCount_eq c h4))
    (nodeCodeFor_decode p (nodeCount_eq c h4) source) factors
    scopeLists scopeNodup scopeMem pairs hpairs

end SubexponentialSAT.Subexp.ComputedMachineSource

end OAI.Algorithms
