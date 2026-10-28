import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBankEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedLayoutChoices

namespace OAI.Algorithms

/-!
# The computed layout in the physical global-bank order

The successful local pairs use the actual side and joint enumerations of
the byte producer. Their explicit global matrices and the matrix-image
program's coefficient order determine the enumeration. This file proves
that its subspaces are exactly the spaces of the computed layout; no
caller-supplied space equality or canonical side order is required.
-/

namespace SubexponentialSAT.Subexp.ComputedGlobalEnumeration

open scoped BigOperators
open MulticolorTypes ConstructivePacking ComputedLayout BlockSearch
open GlobalBasis GlobalKernel BlockwiseEnumeration BlockCoefficientProgram

section Transport

variable {p D k Δ r : ℕ} {τ : ℚ} [Fact p.Prime]
variable {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
variable {P : Factor.Pattern (Fin D) F} {c : SubexpLayoutSpec.Parameters p k Δ r τ}

/-- The semantic layout appears only in the erased interpretation of the
already constructed coordinate data. -/
def interpret (L : SubexpLayoutSpec.Layout (E := E) P c) (t : Fin c.Q)
    {W : Fin r → Submodule (ZMod p) (Fin D → ZMod p)}
    (raw : LocalData (ZMod p) (Fin D) r W) (hW : W = L.K t) :
    SubexpLayoutSpec.EnumerationData L t := by
  let data : LocalData (ZMod p) (Fin D) r (L.K t) :=
    cast (congrArg (fun W => LocalData (ZMod p) (Fin D) r W) hW) raw
  exact {
    outerCount := data.outerCount
    innerCount := data.innerCount
    outerBase := data.outerBase
    incrementEquiv := data.incrementEquiv
    assignmentEquiv := data.assignmentEquiv
    reconstruction := data.reconstruction }

theorem interpret_outerBanks (L : SubexpLayoutSpec.Layout (E := E) P c) (t : Fin c.Q)
    {W : Fin r → Submodule (ZMod p) (Fin D → ZMod p)}
    (raw : LocalData (ZMod p) (Fin D) r W) (hW : W = L.K t) :
    (List.ofFn (interpret L t raw hW).outerBase).map
      (fun v => (vectorWords p v).flatten) =
      (List.ofFn raw.outerBase).map (fun v => (vectorWords p v).flatten) := by
  cases hW
  rfl

theorem interpret_innerBanks (L : SubexpLayoutSpec.Layout (E := E) P c) (t : Fin c.Q)
    {W : Fin r → Submodule (ZMod p) (Fin D → ZMod p)}
    (raw : LocalData (ZMod p) (Fin D) r W) (hW : W = L.K t) (g : Fin r) :
    (List.ofFn (fun i => ((interpret L t raw hW).incrementEquiv g i).val)).map
      (fun v => (vectorWords p v).flatten) =
      (List.ofFn (fun i => (raw.incrementEquiv g i).val)).map
        (fun v => (vectorWords p v).flatten) := by
  cases hW
  rfl

end Transport

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
variable (t : Fin c.Q) {n m : Fin r → ℕ}
variable (rowE : ∀ g, Fin (m g) ≃ ((i : Fin Δ) × Joint t g i))
variable (colE : ∀ g, Fin (n g) ≃ Side (Δ := Δ) t g)

/-- The same dynamic-programming joint matrices whose entries the physical
constraint producer writes. -/
def jointMaps (g : Fin r) (i : Fin Δ) :
    (Joint t g i → ZMod p) →ₗ[ZMod p] (Joint t g i → ZMod p) :=
  (ElementaryMatrix.jointMatrixDP i t g c.R
    (CoefficientSearch.coefficientsNat p A c.R)).mulVecLin

def constraints (g : Fin r) : Fin (m g) → Fin (n g) → ZMod p :=
  universalConstraint t (jointMaps c A t) rowE colE g

variable (pairs : ∀ g, Candidate (ZMod p) (n g) × Candidate (ZMod p) (n g))
variable (good : ∀ g, GoodPair (constraints c A t rowE colE g) (pairs g))

local notation "BPack" => packingWithWords P slots vertices types indices a tail
local notation "L" => layoutWithWordsOfTail P c hP hsize hthreshold hE nodes slots
  vertices types indices a tail haNodup haFull A htail

/-- These are exactly the matrices used in the raw bank enumeration. -/
def outerMatrix : Fin D →
    Fin (outerList (b := (BPack).blockCount) (l := (BPack).leftovers.length) pairs).length → ZMod p :=
  GlobalBasis.outerMatrix (fun u : UniversalType r c.Q Δ => u.head t) colE
    (constraints c A t rowE colE) pairs good (QuarticSearch.elements p)
    (QuarticSearch.mem_elements p) (BPack).completeBlocks.embed (BPack).leftoverEquiv

def innerMatrix (g : Fin r) : Fin D →
    Fin (innerList (b := (BPack).blockCount) pairs g).length → ZMod p :=
  GlobalBasis.innerMatrix (fun u : UniversalType r c.Q Δ => u.head t) colE
    (constraints c A t rowE colE) pairs good (QuarticSearch.elements p)
    (QuarticSearch.mem_elements p) (BPack).completeBlocks.embed (BPack).leftoverEquiv g

def rawData : LocalData (ZMod p) (Fin D) r
    (fun g => ComputedBlockwiseEnumeration.packedSpace (BPack).completeBlocks.embed
      (sideKernel (fun u : UniversalType r c.Q Δ => u.head t) colE
        (constraints c A t rowE colE) g)) :=
  GlobalBankEnumeration.computedData (fun u : UniversalType r c.Q Δ => u.head t) colE
    (constraints c A t rowE colE) pairs good (QuarticSearch.elements p)
    (QuarticSearch.mem_elements p) (BPack).completeBlocks.embed (BPack).leftoverEquiv

theorem rawSpace_eq_layout :
    (fun g => ComputedBlockwiseEnumeration.packedSpace (BPack).completeBlocks.embed
      (sideKernel (fun u : UniversalType r c.Q Δ => u.head t) colE
        (constraints c A t rowE colE) g)) = (L).K t := by
  funext g
  rw [ComputedBlockwiseEnumeration.packedSpace_eq,
    sideKernel_eq_supported (fun u : UniversalType r c.Q Δ => u.head t) colE
      (constraints c A t rowE colE) g (joint t g) (joint_subset_side t g)
      (jointMaps c A t g) (rowE g) rfl]
  have hm : jointMaps c A t g = (fun i =>
      (MatrixSupport.jointMatrix i t g c.R
        (CoefficientSearch.coefficientsNat p A c.R)).mulVecLin) := by
    funext i
    exact congrArg (fun M : Matrix (Joint t g i) (Joint t g i) (ZMod p) => M.mulVecLin)
      (ElementaryMatrix.jointMatrixDP_eq i t g c.R
        (CoefficientSearch.coefficientsNat p A c.R))
  exact congrArg (fun M => DirectSums.packedSubspace (BPack).completeBlocks.embed
    (SubspaceDimension.universalFixedSpace t g M)) hm

/-- Actual local search results, arbitrary actual fiber order, and actual
matrix-image order yield the computed layout's full enumeration contract. -/
def enumeration : SubexpLayoutSpec.EnumerationData L t := by
  let raw := rawData P c slots vertices types indices a tail A t rowE colE pairs good
  have hW := rawSpace_eq_layout P c hP hsize hthreshold hE nodes slots vertices types indices
    a tail haNodup haFull A htail t rowE colE
  let data : LocalData (ZMod p) (Fin D) r ((L).K t) :=
    cast (congrArg (fun W => LocalData (ZMod p) (Fin D) r W) hW) raw
  exact {
    outerCount := data.outerCount
    innerCount := data.innerCount
    outerBase := data.outerBase
    incrementEquiv := data.incrementEquiv
    assignmentEquiv := data.assignmentEquiv
    reconstruction := data.reconstruction }

theorem outerBanks_eq :
    (List.ofFn (enumeration P c hP hsize hthreshold hE nodes slots vertices types indices
      a tail haNodup haFull A htail t rowE colE pairs good).outerBase).map
      (fun v => (vectorWords p v).flatten) =
      MatrixImageEnumeration.bankRecords p
        (outerMatrix P c slots vertices types indices a tail A t rowE colE pairs good) := by
  exact (interpret_outerBanks L t
    (rawData P c slots vertices types indices a tail A t rowE colE pairs good)
    (rawSpace_eq_layout P c hP hsize hthreshold hE nodes slots vertices types indices
      a tail haNodup haFull A htail t rowE colE)).trans
    (GlobalBankEnumeration.computedData_outerBankRecords_eq
      (fun u : UniversalType r c.Q Δ => u.head t) colE
      (constraints c A t rowE colE) pairs good (QuarticSearch.elements p)
      (QuarticSearch.mem_elements p) (BPack).completeBlocks.embed (BPack).leftoverEquiv)

theorem innerBanks_eq (g : Fin r) :
    (List.ofFn (fun i => ((enumeration P c hP hsize hthreshold hE nodes slots vertices types indices
      a tail haNodup haFull A htail t rowE colE pairs good).incrementEquiv g i).val)).map
      (fun v => (vectorWords p v).flatten) =
      MatrixImageEnumeration.bankRecords p
        (innerMatrix P c slots vertices types indices a tail A t rowE colE pairs good g) := by
  exact (interpret_innerBanks L t
    (rawData P c slots vertices types indices a tail A t rowE colE pairs good)
    (rawSpace_eq_layout P c hP hsize hthreshold hE nodes slots vertices types indices
      a tail haNodup haFull A htail t rowE colE) g).trans
    (GlobalBankEnumeration.computedData_innerBankRecords_eq
      (fun u : UniversalType r c.Q Δ => u.head t) colE
      (constraints c A t rowE colE) pairs good (QuarticSearch.elements p)
      (QuarticSearch.mem_elements p) (BPack).completeBlocks.embed (BPack).leftoverEquiv g)

end ActualLayout

end SubexponentialSAT.Subexp.ComputedGlobalEnumeration

end OAI.Algorithms
