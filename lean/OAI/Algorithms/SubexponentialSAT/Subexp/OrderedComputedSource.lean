import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.OrderedScopeSystem
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedMachineSource

namespace OAI.Algorithms

/-!
# Computed source data in the emitted physical factor order

The original factor enumeration and scope lists determine the numeric
system, its incidence slots, and the factor/head/padding seed order. The
quartic node order is the actual represented machine order. The final
count is transported back to the original factor system.

This is a constructor and a represented reference computation. Its physical
implementation and primitive runtime remain separate obligations.
-/

noncomputable section

namespace SubexponentialSAT.Subexp.OrderedComputedSource

open SubexponentialSAT.MulticolorTypes ConstructivePacking ComputedLayout ComputedLayoutEnumeration
open SubexpSelectedConversions SubexpLayoutSpec RepresentedNodeOrder

def finOrder (n : ℕ) : FiniteEnumeration (Fin n) :=
  ⟨List.finRange n, List.nodup_finRange n, List.mem_finRange⟩

def seedOrder (D E Δ : ℕ) :
    FiniteEnumeration (SubexpTypeVariance.SeedIndex (Fin D) (Fin E) Δ) where
  values := AssignmentEnumeration.seedIndices (List.finRange D) (List.finRange E) Δ
  nodup := AssignmentEnumeration.seedIndices_nodup _ _ _
    (List.nodup_finRange D) (List.nodup_finRange E)
  complete := AssignmentEnumeration.mem_seedIndices _ _ _ List.mem_finRange List.mem_finRange

variable {D p k Δ r : ℕ} {τ : ℚ} [Fact p.Prime] [NeZero r]
variable {F : Type*} [Fintype F] [DecidableEq F]
variable (S : Factor.System (Fin D) F (ZMod p))
variable (factors : FiniteEnumeration F) (scopeLists : F → List (Fin D))
variable (scopeNodup : ∀ e, (scopeLists e).Nodup)
variable (scopeMem : ∀ e v, v ∈ scopeLists e ↔ v ∈ S.scope e)
variable (c : Parameters p k Δ r τ) (h4 : c.h = 4)
variable (hP : S.toPattern.Bounded k Δ) (hsize : c.Dstar ≤ D)
variable (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ)^3 *
  (1 + (Δ * k : ℕ)) ≤ τ^2 * c.Dstar)
variable (types : FiniteEnumeration (UniversalType r c.Q Δ))
variable (a : Word r c.Q) (tail : List (Word r c.Q))
variable (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
variable (A : ℕ) (htail : SpectralRank.normalizedTail r (c.Q - 1) A c.R ≤ τ / (Δ : ℚ))
variable (source : Prepared p 0) (target : Prepared p D)
variable (pairs : ∀ t : Fin c.Q, SidePairs p r c.Q Δ t)
variable (hpairs : ∀ (t : Fin c.Q) (g : Fin r),
  BlockSearch.GoodPair
    (LocalEnumeration.canonicalConstraintMatrix (Δ := Δ) t g c.R
      (CoefficientSearch.coefficientsNat p A c.R)) (pairs t g))

local notation "E₀" => List.length (OrderedScopeSystem.rawScopes factors scopeLists)
local notation "S₀" => OrderedScopeSystem.system S factors scopeLists scopeMem
local notation "P₀" => OrderedScopeSystem.bounded S factors scopeLists scopeMem hP
local notation "slots₀" => OrderedScopeSystem.slots S factors scopeLists scopeMem hP
local notation "L" => layoutWithWordsOfTail (Factor.System.toPattern S₀) c P₀
  (ComputedSource.fin_size hsize) hthreshold
  (ComputedMachineSource.extension_degree c h4)
  (nodesFor p (ComputedMachineSource.nodeCount_eq c h4)) slots₀
  (finOrder D) types (seedOrder D E₀ Δ) a tail haNodup haFull A htail

omit [Fintype F] in
/-- Reindexing the factor preserves its complete physical table-row stream.
The same scope list determines every local coordinate by occurrence rank. -/
theorem orderedRows_system {C : Type*} (e : Fin E₀) (zero one : C) :
    SubexpLeafTables.orderedRows S₀ e
      (ComputedSource.scopeIndex S₀
        (fun i => scopeLists (OrderedScopeSystem.factorEquiv factors scopeLists i))
        (fun i => scopeNodup (OrderedScopeSystem.factorEquiv factors scopeLists i))
        (OrderedScopeSystem.scopeLists_mem S factors scopeLists scopeMem) e) zero one =
      SubexpLeafTables.orderedRows S (OrderedScopeSystem.factorEquiv factors scopeLists e)
        (ComputedSource.scopeIndex S scopeLists scopeNodup scopeMem
          (OrderedScopeSystem.factorEquiv factors scopeLists e)) zero one := by
  rfl

/-- No arbitrary slots, factor IDs, node-code decoder identity, or local
table/polynomial identity is a parameter of this constructor. -/
def input : SubexpCountSource.SourceInput S₀ L source.residueRing target.ring :=
  ComputedMachineSource.input S₀ c h4 P₀ hsize hthreshold slots₀
    (finOrder D) types (seedOrder D E₀ Δ) a tail haNodup haFull A htail source target
    (finOrder E₀)
    (fun e => scopeLists (OrderedScopeSystem.factorEquiv factors scopeLists e))
    (fun e => scopeNodup (OrderedScopeSystem.factorEquiv factors scopeLists e))
    (OrderedScopeSystem.scopeLists_mem S factors scopeLists scopeMem) pairs hpairs

/-- The represented reference computation on the physically indexed system. -/
def run : List (SubexpSymbolicCost.QuarticCode p D) × ℕ :=
  SubexpCountExecution.runSelected S₀ L source.residueRing target.ring
    (SubexpSelectedSource.toSelectedInput S₀ L source target
      (input S factors scopeLists scopeNodup scopeMem c h4 hP hsize hthreshold
        types a tail haNodup haFull A htail source target pairs hpairs))

/-- The numeric factor IDs and computed incidence slots preserve the full
natural-number count of the original leaf system. -/
theorem run_decodeCount (hD : 0 < D) :
    SubexpActualRing.decodeCount p (D + 1) (Nat.succ_pos D)
      ((PolynomialAlgorithm.denote
        ((run S factors scopeLists scopeNodup scopeMem c h4 hP hsize hthreshold
          types a tail haNodup haFull A htail source target pairs hpairs).1.map
          target.ring.decode)).coeff 0) = Factor.count S :=
  (SubexpSelectedSource.run_decodeCount S₀ L source target
    (input S factors scopeLists scopeNodup scopeMem c h4 hP hsize hthreshold
      types a tail haNodup haFull A htail source target pairs hpairs) hD).trans
    (OrderedScopeSystem.count_system S factors scopeLists scopeMem)

end SubexponentialSAT.Subexp.OrderedComputedSource

end

end OAI.Algorithms
