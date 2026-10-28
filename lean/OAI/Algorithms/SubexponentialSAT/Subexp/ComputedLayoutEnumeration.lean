import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedLayoutChoices
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedLocalEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedBlockwiseEnumeration

namespace OAI.Algorithms

/-!
# Explicit enumeration data for the layout with runtime choices

Local basis pairs are supplied by their successful finite checks. The global
coordinate maps use only those pairs, block copies, the actual packing lookup,
and the leftover list. Semantic layout values occur only in proof transports.
-/

namespace SubexponentialSAT.Subexp.ComputedLayoutEnumeration

open SubexponentialSAT.MulticolorTypes ConstructivePacking BlockwiseEnumeration
open ComputedLayout ComputedLocalEnumeration LocalEnumeration BlockSearch

abbrev SidePairs (p r Q Δ : ℕ) (t : Fin Q) := (g : Fin r) →
  Candidate (ZMod p) (FiberEnumeration.sideList (Δ := Δ) t g).length ×
    Candidate (ZMod p) (FiberEnumeration.sideList (Δ := Δ) t g).length

section GlobalData

variable {p r Q Δ : ℕ} [Fact p.Prime] [NeZero r]
variable {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]

/-- Executable global data for the exact runtime packing and the supplied
successful side pairs. The target submodules have computable carriers. -/
noncomputable def globalDataForPairs (P : Factor.Pattern V F) (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V) (types : FiniteEnumeration (UniversalType r Q Δ))
    (indices : FiniteEnumeration (SubexpTypeVariance.SeedIndex V F Δ))
    (a : Word r Q) (tail : List (Word r Q))
    (t : Fin Q) (R : ℕ) (coeff : ℕ → ZMod p) (pairs : SidePairs p r Q Δ t)
    (hpairs : ∀ g, GoodPair (canonicalConstraintMatrix (Δ := Δ) t g R coeff) (pairs g)) :
    LocalData (ZMod p) V r (fun g => ComputedBlockwiseEnumeration.packedSpace
      (packingWithWords P slots vertices types indices a tail).completeBlocks.embed
      (canonicalSpace t g R coeff)) :=
  ComputedBlockwiseEnumeration.computedData
    (packingWithWords P slots vertices types indices a tail).completeBlocks.embed
    (executableLocalDataForPairs t R coeff pairs hpairs)
    (packingWithWords P slots vertices types indices a tail).leftoverEquiv

end GlobalData

section LayoutData

variable {p k Δ r : ℕ} {τ : ℚ} [Fact p.Prime] [NeZero r]
variable {V F E : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable [Field E] [Algebra (ZMod p) E]

/-- The explicit maps above inhabit the actual layout's enumeration contract.
This is an ordinary executable definition; only the correctness transport
mentions the semantic layout or its abstract submodule construction. -/
noncomputable def enumerationForPairs (P : Factor.Pattern V F)
    (c : SubexpLayoutSpec.Parameters p k Δ r τ)
    (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card V)
    (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
      (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar)
    (hE : Module.finrank (ZMod p) E = c.h)
    (nodes : Fin c.Q ≃ {z : E // z ≠ 0})
    (slots : SlotAssignment.SlotMap P Δ)
    (vertices : FiniteEnumeration V) (types : FiniteEnumeration (UniversalType r c.Q Δ))
    (indices : FiniteEnumeration (SubexpTypeVariance.SeedIndex V F Δ))
    (a : Word r c.Q) (tail : List (Word r c.Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (A : ℕ) (htail : SpectralRank.normalizedTail r (c.Q - 1) A c.R ≤ τ / (Δ : ℚ))
    (t : Fin c.Q) (pairs : SidePairs p r c.Q Δ t)
    (hpairs : ∀ g, GoodPair (canonicalConstraintMatrix (Δ := Δ) t g c.R
      (CoefficientSearch.coefficientsNat p A c.R)) (pairs g)) :
    SubexpLayoutSpec.EnumerationData
      (layoutWithWordsOfTail P c hP hsize hthreshold hE nodes slots
        vertices types indices a tail haNodup haFull A htail) t := by
  let raw := globalDataForPairs P slots vertices types indices a tail t c.R
    (CoefficientSearch.coefficientsNat p A c.R) pairs hpairs
  have hK : (fun g => ComputedBlockwiseEnumeration.packedSpace
      (packingWithWords P slots vertices types indices a tail).completeBlocks.embed
      (canonicalSpace t g c.R (CoefficientSearch.coefficientsNat p A c.R))) =
      (layoutWithWordsOfTail P c hP hsize hthreshold hE nodes slots
        vertices types indices a tail haNodup haFull A htail).K t := by
    funext g
    rw [ComputedBlockwiseEnumeration.packedSpace_eq, canonicalSpace_eq]
    rfl
  let data : LocalData (ZMod p) V r
      ((layoutWithWordsOfTail P c hP hsize hthreshold hE nodes slots
        vertices types indices a tail haNodup haFull A htail).K t) :=
    cast (congrArg (fun W => LocalData (ZMod p) V r W) hK) raw
  exact {
    outerCount := data.outerCount
    innerCount := data.innerCount
    outerBase := data.outerBase
    incrementEquiv := data.incrementEquiv
    assignmentEquiv := data.assignmentEquiv
    reconstruction := data.reconstruction }

end LayoutData

end SubexponentialSAT.Subexp.ComputedLayoutEnumeration

end OAI.Algorithms
