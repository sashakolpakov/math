import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.RawTemplateRefinement
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedLayoutChoices
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationCode

namespace OAI.Algorithms

/-!
# The raw template uses the computed layout's exact coordinate lists

Both sides scan the ambient indices in ascending order. The identities
below identify the lists themselves, not merely their underlying sets.
-/

namespace SubexponentialSAT.Subexp.RawTemplateSupports

open MulticolorTypes ConstructivePacking SupportSelectionProgram
open RawTemplateRefinement ComputedLayout

theorem outsideSupport_eq_outsideCoordinates {D r Q Δ : ℕ}
    (packing : PackingData (Fin D) (UniversalType r Q Δ)) (t : Fin Q) :
    outsideSupport packing =
      SubexpComputedWeights.outsideCoordinates (colorSupport packing t) := by
  unfold outsideSupport SubexpComputedWeights.outsideCoordinates
  apply List.filter_congr
  intro v _
  have hmem : v ∈ Finset.univ.biUnion (fun g => (colorSupport packing t g).toFinset) ↔
      v ∈ Set.range packing.completeBlocks.embed := by
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset]
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨j, u, _, he⟩ := (DirectSums.mem_packedSupportFinset
        packing.completeBlocks.embed (side (Δ := Δ) t g).toFinset v).mp
        ((mem_colorSupport packing t g v).mp hg)
      exact ⟨(j, u), he⟩
    · rintro ⟨⟨j, u⟩, rfl⟩
      refine ⟨u.head t, (mem_colorSupport packing t (u.head t) _).mpr ?_⟩
      exact (DirectSums.mem_packedSupportFinset packing.completeBlocks.embed
        (side (Δ := Δ) t (u.head t)).toFinset _).mpr
        ⟨j, u, by simp only [Set.mem_toFinset, mem_side], rfl⟩
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, SupportSelectionSemantics.outsideAt_true_iff, hmem]

section Enumeration

variable {p D k Δ r : ℕ} {τ : ℚ} [Fact p.Prime]
variable {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
variable {P : Factor.Pattern (Fin D) F} {c : SubexpLayoutSpec.Parameters p k Δ r τ}

theorem blocksOfEnumeration_eq (L : SubexpLayoutSpec.Layout (E := E) P c)
    (t : Fin c.Q) (packing : PackingData (Fin D) (UniversalType r c.Q Δ))
    (data : SubexpLayoutSpec.EnumerationData L t)
    (factors : List F) (words : F → Word r c.Q)
    (packets : F → SubexpTemplateFactors.Factor p D) :
    blocksOfEnumeration L t packing data factors words packets =
      blocks packing t factors words packets (SubexpEnumerationCode.outerBases data)
        (SubexpEnumerationCode.innerIncrements data) := rfl

end Enumeration

section ActualLayout

variable {p D k Δ r : ℕ} {τ : ℚ} [Fact p.Prime] [NeZero r]
variable {F E : Type*} [Fintype F] [DecidableEq F] [Field E] [Algebra (ZMod p) E]
variable (P : Factor.Pattern (Fin D) F) (c : SubexpLayoutSpec.Parameters p k Δ r τ)
variable (hP : P.Bounded k Δ) (hsize : c.Dstar ≤ Fintype.card (Fin D))
variable (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ) ^ 3 *
  (1 + (Δ * k : ℕ)) ≤ τ ^ 2 * c.Dstar)
variable (hE : Module.finrank (ZMod p) E = c.h)
variable (nodes : Fin c.Q ≃ {z : E // z ≠ 0})
variable (slots : SlotAssignment.SlotMap P Δ)
variable (vertices : FiniteEnumeration (Fin D))
variable (types : FiniteEnumeration (UniversalType r c.Q Δ))
variable (indices : FiniteEnumeration (SubexpTypeVariance.SeedIndex (Fin D) F Δ))
variable (a : Word r c.Q) (tail : List (Word r c.Q))
variable (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
variable (A : ℕ) (htail : SpectralRank.normalizedTail r (c.Q - 1) A c.R ≤ τ / (Δ : ℚ))

local notation "BPack" => packingWithWords P slots vertices types indices a tail
local notation "L" => layoutWithWordsOfTail P c hP hsize hthreshold hE nodes slots
  vertices types indices a tail haNodup haFull A htail

/-- The support selector and the reference source use the same increasing
ambient list for every color of the actual computed layout. -/
theorem colorSupport_eq (t : Fin c.Q) (g : Fin r) :
    colorSupport BPack t g = SubexpEnumerationCode.supportLists L t g := by
  unfold colorSupport SubexpEnumerationCode.supportLists
  apply List.filter_congr
  intro v _
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, SupportSelectionSemantics.colorAt_eq_supportAt]
  exact ComputedLayout.supportAt_iff BPack (MulticolorTypes.side (Δ := Δ) t g).toFinset v

theorem outsideSupport_eq (t : Fin c.Q) :
    outsideSupport BPack = SubexpEnumerationCode.outsideList L t := by
  rw [outsideSupport_eq_outsideCoordinates BPack t]
  unfold SubexpEnumerationCode.outsideList
  apply congrArg SubexpComputedWeights.outsideCoordinates
  funext g
  exact colorSupport_eq P c hP hsize hthreshold hE nodes slots vertices types indices
    a tail haNodup haFull A htail t g

end ActualLayout

end SubexponentialSAT.Subexp.RawTemplateSupports

end OAI.Algorithms
