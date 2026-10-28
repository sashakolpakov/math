import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMatrixBytes
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedGlobalEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.RawTemplateRefinement
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBankRuntimeBound

namespace OAI.Algorithms

/-!
# The produced bank bundle is the computed layout's enumeration

This is the aggregate form of the per-matrix bank identities. It uses the
same actual local tables, side order, packing and coefficient order on both
sides, including the outer matrix followed by ascending colors.
-/

namespace SubexponentialSAT.Subexp.ComputedBankBundle

open MulticolorTypes ConstructivePacking ComputedLayout BlockSearch

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
variable (C : GlobalBasisInput.Context p r c.Q Δ) (hr : 0 < r) (hQ : 0 < c.Q)
variable (hsplit : ∀ g, (C.tables g).split ≤ (C.tables g).dimension)
variable {m : Fin r → ℕ}
variable (rowE : ∀ g, Fin (m g) ≃ ((i : Fin Δ) × Joint C.position g i))

local notation "BPack" => packingWithWords P slots vertices types indices a tail
local notation "Cols" => GlobalBasisRefinement.sideIndex C hr hQ
local notation "Pairs" => GlobalBasisRefinement.pairs C hsplit
local notation "Constraints" => ComputedGlobalEnumeration.constraints c A C.position rowE Cols

variable (good : ∀ g,
  GoodPair
    (ComputedGlobalEnumeration.constraints c A C.position rowE
      (GlobalBasisRefinement.sideIndex C hr hQ) g)
    (GlobalBasisRefinement.pairs C hsplit g))

local notation "CData" => ComputedGlobalEnumeration.enumeration P c hP hsize hthreshold hE
  nodes slots vertices types indices a tail haNodup haFull A htail C.position rowE Cols Pairs good
local notation "Images" => GlobalBasisMatrixBytes.images C hr hQ hsplit Constraints good
  (QuarticSearch.elements p) (QuarticSearch.mem_elements p) BPack

/-- The pre-encoding bank lists have exactly the enumeration's array order.
This form also supplies the matrix-image runtime bound's array hypothesis. -/
theorem arrays_eq :
    (Images).map (fun M => MatrixImageEnumeration.bankRecords p M.entries) =
      SubexpNodeBankBounds.outerBanks CData :: SubexpNodeBankBounds.innerBanks CData := by
  simp only [GlobalBasisMatrixBytes.images, List.map_cons, List.map_ofFn, Function.comp_def]
  apply congrArg₂ List.cons
  · exact (ComputedGlobalEnumeration.outerBanks_eq P c hP hsize hthreshold hE nodes slots
      vertices types indices a tail haNodup haFull A htail C.position rowE Cols Pairs good).symm
  · apply congrArg List.ofFn
    funext g
    exact (ComputedGlobalEnumeration.innerBanks_eq P c hP hsize hthreshold hE nodes slots
      vertices types indices a tail haNodup haFull A htail C.position rowE Cols Pairs good g).symm

theorem bankLists_eq :
    (Images).map SubexpNodeBankMap.bankList =
      ProgramEncoding.encodeRecords (SubexpNodeBankBounds.outerBanks CData) ::
        (SubexpNodeBankBounds.innerBanks CData).map ProgramEncoding.encodeRecords := by
  change (Images).map (fun M => ProgramEncoding.encodeRecords
    (MatrixImageEnumeration.bankRecords p M.entries)) = _
  have h := congrArg (List.map ProgramEncoding.encodeRecords)
    (arrays_eq P c hP hsize hthreshold hE nodes slots vertices types indices
      a tail haNodup haFull A htail C hr hQ hsplit rowE good)
  simpa only [List.map_map, List.map_cons, Function.comp_def] using h

/-- Literal bytes consumed by the raw-template producer, with no additional
array-order or bank-equality premise. -/
theorem bankBundle_eq :
    ProgramEncoding.encodeRecords ((Images).map SubexpNodeBankMap.bankList) =
      SubexpRawTemplate.bankBundle
        ((List.ofFn (CData).outerBase).map RawTemplateRefinement.vectorBytes)
        (List.ofFn fun g =>
          (List.ofFn fun i => ((CData).incrementEquiv g i).val).map
            RawTemplateRefinement.vectorBytes) := by
  exact congrArg ProgramEncoding.encodeRecords
    (bankLists_eq P c hP hsize hthreshold hE nodes slots vertices types indices
      a tail haNodup haFull A htail C hr hQ hsplit rowE good)

/-- Instantiate the published physical bank-mapper bound with the actual
computed enumeration; no array equality remains as a caller hypothesis. -/
theorem runtimeBound_le_iterations :
    SubexpNodeBankMap.runtimeBound Images ≤
      100000 * (SubexpNodeBankRuntimeBound.scale p D) ^ 3 * ((CData).iterationCount + 1) ^ 4 :=
  SubexpNodeBankRuntimeBound.runtimeBound_le_iterations CData Images
    (arrays_eq P c hP hsize hthreshold hE nodes slots vertices types indices
      a tail haNodup haFull A htail C hr hQ hsplit rowE good)

theorem bankBundle_length_le :
    (ProgramEncoding.encodeRecords ((Images).map SubexpNodeBankMap.bankList)).length ≤
      16 * (D * MatrixWordEncoding.width p + 1) * ((CData).iterationCount + 1) := by
  rw [bankBundle_eq P c hP hsize hthreshold hE nodes slots vertices types indices
    a tail haNodup haFull A htail C hr hQ hsplit rowE good]
  exact SubexpNodeBankBounds.bankBundle_length_le CData

end SubexponentialSAT.Subexp.ComputedBankBundle

end OAI.Algorithms
