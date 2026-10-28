import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutSemantics
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchRefinement
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedBankBundle

namespace OAI.Algorithms

/-!
# Enumeration from the actual Main layout output

The local tables are recovered from the emitted batch, in its literal
node/color order. Their proved checker equations identify the same global
spaces as the layout whose rows Main produced. The resulting bank lists
retain the matrix-image program's actual coefficient order.
-/

noncomputable section

namespace SubexponentialSAT.SubexpMainLayoutEnumeration

open SubexpMainProgram SubexpLayoutSpec Subexp
open SubexpLayoutPorts (Allocation master)
open MulticolorTypes

section ActualBatch

variable {er es p r Δ R D : ℕ} [Fact p.Prime] [NeZero r]
variable {alloc : Allocation es} {a middle out : MainState er es}
variable {hregs : 16 ≤ er} {hr : 0 < r} {hQ : 0 < p^4 - 1}
variable {scopes : List (List ℕ)}
variable {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
variable {tables : List (List Bool)}
variable (h : SubexpMainLayoutExecution.Result hregs alloc a middle out
  p r Δ R D hr hQ scopes hd tables)

/-- Interpret the successful records that Main actually stored. -/
def localResults : (t : Fin (p^4 - 1)) → (g : Fin r) →
    LocalBasisBatchRefinement.Result (Δ := Δ) p hr hQ
      (List.ofFn h.choices.coefficients) t g :=
  Classical.choose (LocalBasisBatchRefinement.exists_results h.choices.rowsGood)

theorem localResults_rows : h.choices.rows =
    List.ofFn (fun t => List.ofFn (fun g => (localResults h t g).payload)) :=
  Classical.choose_spec (LocalBasisBatchRefinement.exists_results h.choices.rowsGood)

/-- The physical metadata is the executable packing of the actual assignment. -/
def metadata : List (List Bool × List Bool) :=
  SubexpGlobalRowPacking.records h.choices.packing.packing CollisionProgram.encodeType

def context (t : Fin (p^4 - 1)) : GlobalBasisInput.Context p r (p^4 - 1) Δ :=
  LocalBasisBatchRefinement.context (localResults h) (metadata h) t

theorem context_position (t : Fin (p^4 - 1)) : (context h t).position = t := rfl

theorem context_split_le (t : Fin (p^4 - 1)) (g : Fin r) :
    ((context h t).tables g).split ≤ ((context h t).tables g).dimension :=
  LocalBasisBatchRefinement.context_split_le (localResults h) (metadata h) t g

theorem context_metadata (t : Fin (p^4 - 1)) :
    (context h t).metadata = PackingMetadata.records h.choices.packing.packing
      (fun v => PackingMetadata.unary v.val) CollisionProgram.encodeType := rfl

theorem context_locations (t : Fin (p^4 - 1)) :
    (context h t).locations 0
      (List.ofFn (GlobalBasisRefinement.packingLocation h.choices.packing.packing)) :=
  GlobalBasisRefinement.packing_locations (context h t) h.choices.packing.packing
    (context_metadata h t)

/-- The final retained batch is exactly this family of actual local contexts. -/
theorem basis_master : out.stacks (master alloc 14) =
    ProgramEncoding.encodeRecords (List.ofFn (fun t => (context h t).batch)) :=
  h.basis_master.trans
    (LocalBasisBatchRefinement.batch_bytes (localResults h) (localResults_rows h) (metadata h))

theorem metadata_master : out.stacks (master alloc 13) =
    SelectorProgram.rawRecords (metadata h) :=
  h.packing_master 2

theorem context_good (t : Fin (p^4 - 1)) (g : Fin r) :
    BlockSearch.GoodPair
      (ConstraintMatrixProgram.matrix (Δ := Δ) p hr hQ t g (List.ofFn h.choices.coefficients))
      (GlobalBasisRefinement.pairs (context h t) (context_split_le h t) g) :=
  LocalBasisBatchRefinement.context_good (localResults h) (metadata h) t g

end ActualBatch

section Layout

variable {p k Δ r : ℕ} {τ : ℚ}
variable {er es D : ℕ} [Fact p.Prime] [NeZero r]
variable {alloc : Allocation es} {a middle out : MainState er es}
variable {hregs : 16 ≤ er} {hr : 0 < r} {hQ : 0 < p^4 - 1}
variable {scopes : List (List ℕ)}
variable {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
variable {tables : List (List Bool)}
variable (c : Parameters p k Δ r τ) (h4 : c.h = 4)
variable (h : SubexpMainLayoutExecution.Result hregs alloc a middle out
  p r Δ c.R D hr hQ scopes hd tables)
variable (hP : (IncidencePlanSpec.pattern D scopes).Bounded k Δ)
variable (hsize : c.Dstar ≤ D)
variable (hthreshold : (Fintype.card (UniversalType r (p^4 - 1) Δ) : ℚ)^3 *
  (1 + (Δ * k : ℕ)) ≤ τ^2 * c.Dstar)
variable (htail : SpectralRank.normalizedTail r (p^4 - 1 - 1)
  (TailInterval.intervalStart r (p^4 - 1) c.R) c.R ≤ τ / (Δ : ℚ))

local notation "c₄" => SubexpMainLayoutSemantics.parameters c h4
local notation "L" => SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail
local notation "A" => TailInterval.intervalStart r (p^4 - 1) c.R
local notation "P" => IncidencePlanSpec.pattern D scopes
local notation "slots" => IncidencePlanSpec.slots D Δ scopes hd
local notation "vertices" => OrderedComputedSource.finOrder D
local notation "types" => PackingCanonicalSpec.types hr hQ Δ
local notation "indices" => OrderedComputedSource.seedOrder D scopes.length Δ
local notation "nodes" => SubexpNumericRowSemantics.nodes c₄ rfl
local notation "hE" => ComputedMachineSource.extension_degree c₄ rfl

def constraints (t : Fin (p^4 - 1)) :=
  ComputedGlobalEnumeration.constraints c₄ A t
    (ConstraintMatrixProgram.rowEquiv hr hQ t)
    (GlobalBasisRefinement.sideIndex (context h t) hr hQ)

/-- The actual successful checker tables satisfy this layout's constraints. -/
theorem context_good_normalized (t : Fin (p^4 - 1)) (g : Fin r) :
    BlockSearch.GoodPair (constraints c h4 h t g)
      (GlobalBasisRefinement.pairs (context h t) (context_split_le h t) g) :=
  LocalBasisBatchRefinement.context_good_normalized (localResults h) A c.R
    List.length_ofFn h.coefficient_check (metadata h) t g

/-- The enumeration belongs to the same layout as Main's generated rows. -/
def enumeration (t : Fin (p^4 - 1)) : EnumerationData L t :=
  ComputedGlobalEnumeration.enumeration P c₄ hP (ComputedSource.fin_size hsize)
    hthreshold hE nodes slots vertices types indices h.choices.first h.choices.tail
    h.choices.nodup h.choices.complete A htail t
    (ConstraintMatrixProgram.rowEquiv hr hQ t)
    (GlobalBasisRefinement.sideIndex (context h t) hr hQ)
    (GlobalBasisRefinement.pairs (context h t) (context_split_le h t))
    (context_good_normalized c h4 h t)

def outerImage (t : Fin (p^4 - 1)) : SubexpNodeBankMap.Matrix p D :=
  GlobalBasisMatrixBytes.outerImage (context h t) hr hQ (context_split_le h t)
    (constraints c h4 h t) (context_good_normalized c h4 h t)
    (QuarticSearch.elements p) (QuarticSearch.mem_elements p) h.choices.packing.packing

def innerImage (t : Fin (p^4 - 1)) (g : Fin r) : SubexpNodeBankMap.Matrix p D :=
  GlobalBasisMatrixBytes.innerImage (context h t) hr hQ (context_split_le h t)
    (constraints c h4 h t) (context_good_normalized c h4 h t)
    (QuarticSearch.elements p) (QuarticSearch.mem_elements p) h.choices.packing.packing g

def images (t : Fin (p^4 - 1)) : List (SubexpNodeBankMap.Matrix p D) :=
  GlobalBasisMatrixBytes.images (context h t) hr hQ (context_split_le h t)
    (constraints c h4 h t) (context_good_normalized c h4 h t)
    (QuarticSearch.elements p) (QuarticSearch.mem_elements p) h.choices.packing.packing

theorem images_order (t : Fin (p^4 - 1)) : images c h4 h t =
    outerImage c h4 h t :: List.ofFn (innerImage c h4 h t) := rfl

theorem outerBanks_eq (t : Fin (p^4 - 1)) :
    (List.ofFn (enumeration c h4 h hP hsize hthreshold htail t).outerBase).map
      (fun v => (BlockCoefficientProgram.vectorWords p v).flatten) =
        MatrixImageEnumeration.bankRecords p (outerImage c h4 h t).entries :=
  ComputedGlobalEnumeration.outerBanks_eq P c₄ hP (ComputedSource.fin_size hsize)
    hthreshold hE nodes slots vertices types indices h.choices.first h.choices.tail
    h.choices.nodup h.choices.complete A htail t
    (ConstraintMatrixProgram.rowEquiv hr hQ t)
    (GlobalBasisRefinement.sideIndex (context h t) hr hQ)
    (GlobalBasisRefinement.pairs (context h t) (context_split_le h t))
    (context_good_normalized c h4 h t)

theorem innerBanks_eq (t : Fin (p^4 - 1)) (g : Fin r) :
    (List.ofFn (fun i =>
      ((enumeration c h4 h hP hsize hthreshold htail t).incrementEquiv g i).val)).map
      (fun v => (BlockCoefficientProgram.vectorWords p v).flatten) =
        MatrixImageEnumeration.bankRecords p (innerImage c h4 h t g).entries :=
  ComputedGlobalEnumeration.innerBanks_eq P c₄ hP (ComputedSource.fin_size hsize)
    hthreshold hE nodes slots vertices types indices h.choices.first h.choices.tail
    h.choices.nodup h.choices.complete A htail t
    (ConstraintMatrixProgram.rowEquiv hr hQ t)
    (GlobalBasisRefinement.sideIndex (context h t) hr hQ)
    (GlobalBasisRefinement.pairs (context h t) (context_split_le h t))
    (context_good_normalized c h4 h t) g

theorem matrixBundle_eq (t : Fin (p^4 - 1)) :
    GlobalBasisProgram.bundleBits (context h t) h.choices.packing.packing.blockCount
      h.choices.packing.packing.leftovers.length
      (List.ofFn (GlobalBasisRefinement.packingLocation h.choices.packing.packing)) =
        ProgramEncoding.encodeRecords ((images c h4 h t).map SubexpNodeBankMap.payload) :=
  GlobalBasisMatrixBytes.bundleBits_eq (context h t) hr hQ (context_split_le h t)
    (constraints c h4 h t) (context_good_normalized c h4 h t)
    (QuarticSearch.elements p) (QuarticSearch.mem_elements p) h.choices.packing.packing

theorem arrays_eq (t : Fin (p^4 - 1)) :
    (images c h4 h t).map (fun M => MatrixImageEnumeration.bankRecords p M.entries) =
      SubexpNodeBankBounds.outerBanks (enumeration c h4 h hP hsize hthreshold htail t) ::
        SubexpNodeBankBounds.innerBanks (enumeration c h4 h hP hsize hthreshold htail t) :=
  ComputedBankBundle.arrays_eq P c₄ hP (ComputedSource.fin_size hsize)
    hthreshold hE nodes slots vertices types indices h.choices.first h.choices.tail
    h.choices.nodup h.choices.complete A htail (context h t) hr hQ (context_split_le h t)
    (ConstraintMatrixProgram.rowEquiv hr hQ t) (context_good_normalized c h4 h t)

/-- Exact outer-then-colors bank bytes accepted by the raw-template producer. -/
theorem bankBundle_eq (t : Fin (p^4 - 1)) :
    ProgramEncoding.encodeRecords ((images c h4 h t).map SubexpNodeBankMap.bankList) =
      SubexpRawTemplate.bankBundle
        ((List.ofFn (enumeration c h4 h hP hsize hthreshold htail t).outerBase).map
          RawTemplateRefinement.vectorBytes)
        (List.ofFn fun g =>
          (List.ofFn fun i =>
            ((enumeration c h4 h hP hsize hthreshold htail t).incrementEquiv g i).val).map
              RawTemplateRefinement.vectorBytes) :=
  ComputedBankBundle.bankBundle_eq P c₄ hP (ComputedSource.fin_size hsize)
    hthreshold hE nodes slots vertices types indices h.choices.first h.choices.tail
    h.choices.nodup h.choices.complete A htail (context h t) hr hQ (context_split_le h t)
    (ConstraintMatrixProgram.rowEquiv hr hQ t) (context_good_normalized c h4 h t)

end Layout

end SubexponentialSAT.SubexpMainLayoutEnumeration

end

end OAI.Algorithms
