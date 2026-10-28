import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ResourceBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SupportCountBridge
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LayoutSizes
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrixNatural
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyInventory
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRankMagnitude
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesPacking

/-! The new traversal charges only attained full integer signatures. Its
predecessor rescans and complete-tuple visitors are additive, and the pair
count is bounded by the square of the original ambient support count. These
numerical comparisons use fixed powers of the original explicit cost; they
do not assert a machine execution or supply an evaluator service. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog SignatureTupleDFS SignatureTupleTraversal
open MulticolorTypes Subexp.ConstructivePacking LayoutExactBuckets

noncomputable section
open Classical

/-- Actual owner-fiber multiplicity bounds every retained integer entry,
in the selected-ID order used by the native head loader. -/
theorem selected_integer_entry_le {r Q D n : ℕ}
    (packing : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R B : ℕ) (hAQ : A ≤ Q)
    (hB : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (t : Fin Q) (js : List ℕ) (hjs : ∀ v ∈ js, v < n)
    (j : Fin D) (i : Fin js.length) :
    |LayoutProducedMatrix.literalNat packing owner A R t j.val (js.get i)| ≤
      (B * LayoutProgram.constraintMassBound Q R : ℕ) := by
  have hi : js.get i < n := hjs _ (List.get_mem ..)
  rw [LayoutProducedMatrix.literalNat, dite_eq_left j.isLt, dite_eq_left hi,
    ← Int.natCast_natAbs]
  exact_mod_cast (LayoutSizes.natAbs_literalMatrix_le_fiber
    packing owner A R hAQ t j ⟨js.get i,hi⟩).trans
      (Nat.mul_le_mul_right _ (hB ⟨js.get i,hi⟩))

/-- A selected free head keeps its actual selected width. Restricting the
columns can only lower the rational rank of the canonical full head. -/
theorem selected_representatives_le_rank
    {r Q D n : ℕ} {O : Type*} [CommRing O] {node : Fin Q → O}
    (packing : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t, (packing.label i).head t = head t (owner i))
    (A R B : ℕ) (hAQ : A ≤ Q)
    (hB : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (denom : Oˣ) (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r)
    (js : List ℕ) (hjs : ∀ v ∈ js, v < n)
    (hjshead : ∀ v (hv : v ∈ js), head t ⟨v, hjs v hv⟩ = g) :
    Fintype.card (AttainedSignatures.Representative (AttainedSignatures.integerKey
      (fun (j : Fin D) (i : Fin js.length) =>
        LayoutProducedMatrix.literalNat packing owner A R t j.val (js.get i)))) ≤
      (2 * js.length * (B * LayoutProgram.constraintMassBound Q R) + 1) ^
        LayoutRank.rowRank (pulledConstraints
          (LayoutProducedMatrix.headOwner packing owner head hhead t g)
          (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
            packing.completeBlocks t g)) := by
  have hcard := AttainedSignatures.card_integer_representative_le_rank
    (fun (j : Fin D) (i : Fin js.length) =>
      LayoutProducedMatrix.literalNat packing owner A R t j.val (js.get i))
    (B * LayoutProgram.constraintMassBound Q R)
    (selected_integer_entry_le packing owner A R B hAQ hB t js hjs)
  rw [Nat.card_eq_fintype_card] at hcard
  exact hcard.trans (Nat.pow_le_pow_right (by omega)
    (LayoutProducedMatrix.selected_nat_rank_le packing owner head hhead A R
      denom hdenom units t g js hjs hjshead))

/-- All selected heads share the original rank sum. The Boolean width in
the common height base is their proved balanced maximum, not ambient n. -/
theorem selected_inventory_le_rank
    {r Q D n : ℕ} {O : Type*} [CommRing O] {node : Fin Q → O}
    (packing : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t, (packing.label i).head t = head t (owner i))
    (A R B H : ℕ) (hAQ : A ≤ Q)
    (hB : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (denom : Oˣ) (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q)
    (js : Fin r → List ℕ) (hjs : ∀ g v, v ∈ js g → v < n)
    (hjshead : ∀ g v (hv : v ∈ js g), head t ⟨v, hjs g v hv⟩ = g)
    (hsize : ∀ g, (js g).length ≤ H) :
    (∏ g : Fin r, Fintype.card (AttainedSignatures.Representative
      (AttainedSignatures.integerKey (fun (j : Fin D) (i : Fin (js g).length) =>
        LayoutProducedMatrix.literalNat packing owner A R t j.val ((js g).get i))))) ≤
      (2 * H * (B * LayoutProgram.constraintMassBound Q R) + 1) ^
        (∑ g : Fin r, LayoutRank.rowRank (pulledConstraints
          (LayoutProducedMatrix.headOwner packing owner head hhead t g)
          (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
            packing.completeBlocks t g))) := by
  apply CostAssembly.jointInventory_le_rankSum
  intro g
  apply (selected_representatives_le_rank packing owner head hhead A R B hAQ hB
    denom hdenom units t g (js g) (hjs g) (hjshead g)).trans
  apply Nat.pow_le_pow_left
  gcongr
  exact hsize g

/-- This is the original maximum of the actual selected matrix ranks.
It requires no bucket tables and never replaces that rank by the larger
canonical pullback rank. The key may be any faithful physical encoding. -/
theorem actual_key_inventory_le_maxRank
    {r Q D n : ℕ} {κ : Fin r → Type*}
    (packing : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R B height : ℕ) (hAQ : A ≤ Q)
    (hB : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hheight : B * LayoutProgram.constraintMassBound Q R ≤ height)
    (rows : List (List Bool)) (low : List Bool) (nodes : Finset (Fin Q))
    (t : Fin Q) (ht : t ∈ nodes)
    (key : (g : Fin r) → Fin (2 ^ (LeafHeadSetupProgram.selectedHeads n rows low
      (t.val*r+g.val)).length) → κ g)
    (hkernel : ∀ g x y, key g x = key g y ↔
      AttainedSignatures.integerKey (fun (j : Fin D)
        (i : Fin (LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).length) =>
          LayoutProducedMatrix.literalNat packing owner A R t j.val
            ((LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).get i)) x =
      AttainedSignatures.integerKey (fun (j : Fin D)
        (i : Fin (LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).length) =>
          LayoutProducedMatrix.literalNat packing owner A R t j.val
            ((LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).get i)) y) :
    (∏ g : Fin r, Fintype.card (AttainedSignatures.Representative (key g))) ≤
      (2*n*height+1) ^ CostAssembly.maxTotalRank nodes
        (BucketProgram.ProducedRank.actualRank packing owner A R rows low) := by
  apply CostAssembly.jointInventory_le_maxTotalRank _ _ nodes _ (by omega) ht
  intro g
  let js := LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)
  have hj : ∀ v ∈ js, v < n := HeadIdentifierProgram.chosenIds_bound _ _
  have hn : js.length ≤ n := HeadIdentifierProgram.count_le _ _
  rw [← Nat.card_eq_fintype_card, card_representative_kernel (key g)
    (AttainedSignatures.integerKey (fun (j : Fin D) (i : Fin js.length) =>
      LayoutProducedMatrix.literalNat packing owner A R t j.val (js.get i))) (hkernel g)]
  have hc := AttainedSignatures.card_integer_representative_le_rank
    (fun (j : Fin D) (i : Fin js.length) =>
      LayoutProducedMatrix.literalNat packing owner A R t j.val (js.get i))
    (B * LayoutProgram.constraintMassBound Q R)
    (selected_integer_entry_le packing owner A R B hAQ hB t js hj)
  apply hc.trans
  apply Nat.pow_le_pow_left
  gcongr

/-- The actual query's owner-fiber scan and scheduled height discharge the
entry cap. The exponent is exactly its original queryLabelRows, including
all selected heads and all raw incidence rows. -/
theorem query_inventory_le_labelRows
    (q : LeafQueryFrontend.Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (first : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (t : Fin (LeafProgram.Query.packingProblem q k hg).Q) :
    let p := LeafProgram.Query.packingProblem q k hg
    let R := (LeafParametersProgram.produce (q.input k)).R
    let A := Subexp.TailInterval.intervalStart p.r p.Q R
    let selected := fun g : Fin p.r => LeafHeadSetupProgram.selectedHeads p.n
      (ProducedQueryRank.rows p first tail) (ProducedQueryRank.queryLow q) (t.val*p.r+g.val)
    (∏ g : Fin p.r, Fintype.card (AttainedSignatures.Representative
      (AttainedSignatures.integerKey (fun (j : Fin p.incidences) (i : Fin (selected g).length) =>
        LayoutProducedMatrix.literalNat (ProducedQueryRank.packing p first tail)
          (ProducedQueryRank.owner p) A R t j.val ((selected g).get i))))) ≤
      (2*p.n*ProducedQueryRank.queryHeight q k+1) ^
        ProducedQueryRank.queryLabelRows q k hg first tail := by
  let p := LeafProgram.Query.packingProblem q k hg
  let R := (LeafParametersProgram.produce (q.input k)).R
  let A := Subexp.TailInterval.intervalStart p.r p.Q R
  have hr : 2 ≤ p.r := LeafParametersProgram.produce_r_ge_two _
  have hR : 4 ≤ R := LeafParametersProgram.produce_R_ge_four _
  have hRQ : 4*R ≤ p.Q := hg.2.2.2.2.2.2.2.1
  have hAQ : A ≤ p.Q := by
    have he := Subexp.TailInterval.intervalStart_end_le hr hR hRQ
    dsimp only [A]
    omega
  have hQ : 1 ≤ p.Q := by omega
  have hh : (q.input k).occurrence * LayoutProgram.constraintMassBound p.Q R ≤
      ProducedQueryRank.queryHeight q k := by
    calc
      _ ≤ (q.input k).occurrence * (2*(8*p.Q)^(2*R)) :=
        Nat.mul_le_mul_left _ (LayoutProgram.constraintMassBound_le _ _ hQ)
      _ = _ := by
        change (q.input k).occurrence * (2*(8*(LeafParametersProgram.produce (q.input k)).Q)^(2*R)) = _
        unfold ProducedQueryRank.queryHeight
        dsimp only [R]
        ring
  let selected := fun g : Fin p.r => LeafHeadSetupProgram.selectedHeads p.n
    (ProducedQueryRank.rows p first tail) (ProducedQueryRank.queryLow q) (t.val*p.r+g.val)
  let key := fun g : Fin p.r => AttainedSignatures.integerKey
    (fun (j : Fin p.incidences) (i : Fin (selected g).length) =>
      LayoutProducedMatrix.literalNat (ProducedQueryRank.packing p first tail)
        (ProducedQueryRank.owner p) A R t j.val ((selected g).get i))
  have hk := actual_key_inventory_le_maxRank (r := p.r) (Q := p.Q)
    (D := p.incidences) (n := p.n) (κ := fun _ => Fin p.incidences → ℤ)
    (ProducedQueryRank.packing p first tail)
    (ProducedQueryRank.owner p) A R (q.input k).occurrence
    (ProducedQueryRank.queryHeight q k) hAQ
    (LeafPackingFiberBounds.query_owner_fiber_le q k hg) hh
    (ProducedQueryRank.rows p first tail) (ProducedQueryRank.queryLow q)
    Finset.univ t (Finset.mem_univ t) key (fun _ _ _ => Iff.rfl)
  simpa only [← Nat.card_eq_fintype_card, key, selected, ProducedQueryRank.queryLabelRows,
    ProducedQueryRank.labelRows, p, R, A] using hk

/-- The executed shifted key may be used directly once the actual loader's
full-row kernel identity is applied. The query itself discharges all entry,
height and rank fields; no successful bucket layout is a premise. -/
theorem query_key_inventory_le_labelRows
    (q : LeafQueryFrontend.Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (first : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (t : Fin (LeafProgram.Query.packingProblem q k hg).Q) :
    let p := LeafProgram.Query.packingProblem q k hg
    let R := (LeafParametersProgram.produce (q.input k)).R
    let A := Subexp.TailInterval.intervalStart p.r p.Q R
    let selected := fun g : Fin p.r => LeafHeadSetupProgram.selectedHeads p.n
      (ProducedQueryRank.rows p first tail) (ProducedQueryRank.queryLow q) (t.val*p.r+g.val)
    let matrix := fun (g : Fin p.r) (j : Fin p.incidences) (i : Fin (selected g).length) =>
      LayoutProducedMatrix.literalNat (ProducedQueryRank.packing p first tail)
        (ProducedQueryRank.owner p) A R t j.val ((selected g).get i)
    ∀ {κ : Fin p.r → Type*}
      (key : (g : Fin p.r) → Fin (2 ^ (selected g).length) → κ g),
      (∀ g x y, key g x = key g y ↔
        AttainedSignatures.integerKey (matrix g) x =
          AttainedSignatures.integerKey (matrix g) y) →
      (∏ g : Fin p.r, Fintype.card (AttainedSignatures.Representative (key g))) ≤
        (2*p.n*ProducedQueryRank.queryHeight q k+1) ^
          ProducedQueryRank.queryLabelRows q k hg first tail := by
  dsimp only
  intro κ key hkernel
  apply le_trans ?_ (query_inventory_le_labelRows q k hg first tail t)
  apply Finset.prod_le_prod
  intro g _
  simpa only [Nat.card_eq_fintype_card] using
    (card_representative_kernel (key g) _ (hkernel g)).le

/-- The original explicit record uses the same ambient coefficient-height
base as the actual query rank theorem. This is only a definitional field read. -/
theorem ofPacking_labelBase (q : LeafQueryFrontend.Query) (k B C d qi e : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (first : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)) :
    (ProducedQueryResources.ofPacking q k B C d qi e hg first tail).labelBase =
      2*(LeafProgram.Query.packingProblem q k hg).n*ProducedQueryRank.queryHeight q k+1 := rfl

/-- The same explicit record retains the maximum of actual selected ranks. -/
theorem ofPacking_labelRows (q : LeafQueryFrontend.Query) (k B C d qi e : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (first : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)) :
    (ProducedQueryResources.ofPacking q k B C d qi e hg first tail).labelRows =
      ProducedQueryRank.queryLabelRows q k hg first tail := rfl

/-- A faithful actual emitted-key inventory fits the very same original
resource record that carries the scheduled sqrt-log estimate. No old selector
Origin or successful bucket-layout premise is introduced. -/
theorem query_key_inventory_le_ofPacking
    (q : LeafQueryFrontend.Query) (k B C d qi e : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (first : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (t : Fin (LeafProgram.Query.packingProblem q k hg).Q) :
    let p := LeafProgram.Query.packingProblem q k hg
    let R := (LeafParametersProgram.produce (q.input k)).R
    let A := Subexp.TailInterval.intervalStart p.r p.Q R
    let selected := fun g : ℕ => LeafHeadSetupProgram.selectedHeads p.n
      (ProducedQueryRank.rows p first tail) (ProducedQueryRank.queryLow q) (t.val*p.r+g)
    let matrix := fun (g : Fin p.r) (j : Fin p.incidences)
      (i : Fin (selected g.val).length) =>
      LayoutProducedMatrix.literalNat (ProducedQueryRank.packing p first tail)
        (ProducedQueryRank.owner p) A R t j.val ((selected g.val).get i)
    ∀ {κ : ℕ → Type*}
      (key : (g : ℕ) → Fin (2 ^ (selected g).length) → κ g),
      (∀ (g : Fin p.r) x y, key g.val x = key g.val y ↔
        AttainedSignatures.integerKey (matrix g) x =
          AttainedSignatures.integerKey (matrix g) y) →
      SignatureTupleDFS.prefixCount
        (fun g => Fintype.card (AttainedSignatures.Representative (key g))) p.r ≤
        (ProducedQueryResources.ofPacking q k B C d qi e hg first tail).labelBase ^
          (ProducedQueryResources.ofPacking q k B C d qi e hg first tail).labelRows := by
  dsimp only
  intro κ key hkernel
  rw [ofPacking_labelBase, ofPacking_labelRows]
  unfold SignatureTupleDFS.prefixCount
  rw [← Fin.prod_univ_eq_prod_range]
  exact query_key_inventory_le_labelRows q k hg first tail t (fun g => key g.val) hkernel

/-- These are the actual first-occurrence counts. In particular a traversal
with no heads still has its one empty complete tuple. -/
theorem attained_inventory_pos {h : ℕ → ℕ} {κ : ℕ → Type*}
    (key : (i : ℕ) → Fin (2 ^ h i) → κ i) (levels : ℕ) :
    1 ≤ prefixCount (fun i => Fintype.card (Representatives key i)) levels := by
  apply Finset.one_le_prod
  intro i _
  have hpositive : 0 < Fintype.card (Representatives key i) := by
    simpa only [Nat.card_eq_fintype_card] using
      AttainedSignatures.card_representative_pos (key i) (pow_pos (by omega) _)
  omega

/-- A faithful physical key encoding preserves the rank bound for all raw
integer rows. No tuple of independent row values is enumerated. -/
theorem attained_inventory_le_rank
    {h rows : ℕ → ℕ} {κ : ℕ → Type*}
    (key : (i : ℕ) → Fin (2 ^ h i) → κ i)
    (matrix : (i : ℕ) → Fin (rows i) → Fin (h i) → ℤ)
    (height : ℕ → ℕ) (levels base rankBound : ℕ)
    (hkernel : ∀ i < levels, ∀ x y,
      key i x = key i y ↔ AttainedSignatures.integerKey (matrix i) x =
        AttainedSignatures.integerKey (matrix i) y)
    (hentry : ∀ i < levels, ∀ j v, |matrix i j v| ≤ (height i : ℤ))
    (hbase : ∀ i < levels, 2 * h i * height i + 1 ≤ base)
    (hbasePos : 1 ≤ base)
    (hrank : (∑ i ∈ Finset.range levels, LayoutRank.rowRank (matrix i)) ≤ rankBound) :
    prefixCount (fun i => Fintype.card (Representatives key i)) levels ≤ base ^ rankBound := by
  apply (prefixCount_le_rank _ (fun i => LayoutRank.rowRank (matrix i)) levels base ?_).trans
    (Nat.pow_le_pow_right hbasePos hrank)
  intro i hi
  rw [← Nat.card_eq_fintype_card, card_representative_kernel (key i)
    (AttainedSignatures.integerKey (matrix i)) (hkernel i hi)]
  exact (AttainedSignatures.card_integer_representative_le_rank
    (matrix i) (height i) (hentry i hi)).trans
      (Nat.pow_le_pow_left (hbase i hi) _)

/-- The support and signature factors occur together in the original
explicit budget. Positive actual call, branch and bit counters pay them. -/
theorem support_enumeration_le_sparseWork
    (n J setup calls branches base rows heads headSize bits ordinary : ℕ)
    (hcalls : 1 ≤ calls) (hbranches : 1 ≤ branches) (hbits : 1 ≤ bits) :
    SupportProgram.count n J * CostAssembly.enumerationWork base rows heads headSize ≤
      CostAssembly.sparseWork n J setup calls branches
        (CostAssembly.enumerationWork base rows heads headSize) bits ordinary := by
  have ho : 1 ≤ (ordinary + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hs : SupportProgram.count n J ≤ (SupportProgram.count n J + 1) ^ 4 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  unfold CostAssembly.sparseWork
  calc
    _ = 1 * 1 * CostAssembly.enumerationWork base rows heads headSize * 1 * 1 *
        SupportProgram.count n J := by ring
    _ ≤ calls * branches * CostAssembly.enumerationWork base rows heads headSize *
        bits * (ordinary + 1) ^ 8 * (SupportProgram.count n J + 1) ^ 4 := by gcongr
    _ ≤ _ := Nat.le_add_left _ _

theorem inventory_head_le_enumeration (K H base rows heads headSize : ℕ)
    (hK : K ≤ base ^ rows) (hH : H ≤ headSize) (hheads : 1 ≤ heads) :
    K * 2 ^ H ≤ CostAssembly.enumerationWork base rows heads headSize := by
  unfold CostAssembly.enumerationWork
  calc
    _ ≤ base ^ rows * 2 ^ headSize := Nat.mul_le_mul hK
      (Nat.pow_le_pow_right (by decide) hH)
    _ = base ^ rows * 1 * 2 ^ headSize := by ring
    _ ≤ _ := by gcongr

/-- Both traversal overhead and every complete-tuple visitor are charged
additively. The +1 survives when there are no head levels. -/
theorem pair_tuple_le_sparseWork
    (m n J setup calls branches base rows heads headSize bits ordinary
      P C levels K H visitor : ℕ)
    (hmn : m ≤ n) (hcalls : 1 ≤ calls) (hbranches : 1 ≤ branches)
    (hbits : 1 ≤ bits) (hheads : 1 ≤ heads) (hKpos : 1 ≤ K)
    (hK : K ≤ base ^ rows) (hH : H ≤ headSize)
    (hvisitor : visitor ≤ C * (levels + 1) * 2 ^ H) :
    DifferencePairs.pairCount m J *
        (2 * P * levels * K * 4 ^ H + K * visitor + 1) ≤
      (2 * P + C + 1) * (levels + 1) *
        (CostAssembly.sparseWork n J setup calls branches
          (CostAssembly.enumerationWork base rows heads headSize) bits ordinary) ^ 2 := by
  have hcombined : SupportProgram.count n J * K * 2 ^ H ≤
      CostAssembly.sparseWork n J setup calls branches
        (CostAssembly.enumerationWork base rows heads headSize) bits ordinary := by
    calc
      _ = SupportProgram.count n J * (K * 2 ^ H) := by ring
      _ ≤ SupportProgram.count n J * CostAssembly.enumerationWork base rows heads headSize :=
        Nat.mul_le_mul_left _ (inventory_head_le_enumeration K H base rows heads headSize
          hK hH hheads)
      _ ≤ _ := support_enumeration_le_sparseWork _ _ _ _ _ _ _ _ _ _ _
        hcalls hbranches hbits
  calc
    _ ≤ SupportProgram.count n J ^ 2 *
        (2 * P * levels * K * 4 ^ H + K * visitor + 1) :=
      Nat.mul_le_mul_right _ (pairCount_le_ambient_support_square hmn J)
    _ ≤ (2 * P + C + 1) * (levels + 1) *
        (SupportProgram.count n J * K * 2 ^ H) ^ 2 :=
      streamedPairTupleCost_le P C levels K H _ visitor hKpos hvisitor
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcombined 2)

/-- The original assembled record already contains positive hash-call and
high-incidence branch counters. Only its actual bit/head positivity remains. -/
theorem pair_tuple_le_assembledWork
    (k m n : ℕ) (p : CostAssembly.Resources) (P C levels K H visitor : ℕ)
    (hmn : m ≤ n) (hbits : 1 ≤ p.bits) (hheads : 1 ≤ p.heads)
    (hKpos : 1 ≤ K) (hK : K ≤ p.labelBase ^ p.labelRows) (hH : H ≤ p.headSize)
    (hvisitor : visitor ≤ C * (levels + 1) * 2 ^ H) :
    DifferencePairs.pairCount m (CostAssembly.jetOrder k n p) *
        (2 * P * levels * K * 4 ^ H + K * visitor + 1) ≤
      (2 * P + C + 1) * (levels + 1) * CostAssembly.assembledWork k n p ^ 2 := by
  exact pair_tuple_le_sparseWork m n (CostAssembly.jetOrder k n p) p.setup
    (CostAssembly.hashCalls n p.clauses
      (SparseCode.distanceDenom p.clauses p.initialOccurrence)) (2 ^ p.branchVars)
    p.labelBase p.labelRows p.heads p.headSize p.bits p.ordinary P C levels K H visitor hmn
    (by unfold CostAssembly.hashCalls; omega)
    (Nat.one_le_pow _ _ (by decide)) hbits hheads hKpos hK hH hvisitor

/-- The measured cursor-event total is connected directly to the original
budget through actual attained full-key cardinalities and their row ranks. -/
theorem pair_events_le_assembledWork
    {h dimensions : ℕ → ℕ} {κ : ℕ → Type*}
    (key : (i : ℕ) → Fin (2 ^ h i) → κ i)
    (matrix : (i : ℕ) → Fin (dimensions i) → Fin (h i) → ℤ)
    (height : ℕ → ℕ) (k m n : ℕ) (p : CostAssembly.Resources)
    (P C levels H visitor : ℕ)
    (hmn : m ≤ n) (hbits : 1 ≤ p.bits) (hheads : 1 ≤ p.heads)
    (hkernel : ∀ i < levels, ∀ x y,
      key i x = key i y ↔ AttainedSignatures.integerKey (matrix i) x =
        AttainedSignatures.integerKey (matrix i) y)
    (hentry : ∀ i < levels, ∀ j v, |matrix i j v| ≤ (height i : ℤ))
    (hbase : ∀ i < levels, 2 * h i * height i + 1 ≤ p.labelBase)
    (hbasePos : 1 ≤ p.labelBase)
    (hrank : (∑ i ∈ Finset.range levels, LayoutRank.rowRank (matrix i)) ≤ p.labelRows)
    (hh : ∀ i < levels, h i ≤ H) (hH : H ≤ p.headSize)
    (hvisitor : visitor ≤ C * (levels + 1) * 2 ^ H) :
    DifferencePairs.pairCount m (CostAssembly.jetOrder k n p) *
        (eventTotal key levels (costWeight key levels P visitor) + 1) ≤
      (2 * P + C + 1) * (levels + 1) * CostAssembly.assembledWork k n p ^ 2 := by
  have hK := attained_inventory_le_rank key matrix height levels p.labelBase p.labelRows
    hkernel hentry hbase hbasePos hrank
  exact (Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (eventTotal_cost_le h key levels P visitor H hh) 1)).trans
      (pair_tuple_le_assembledWork k m n p P C levels _ H visitor hmn hbits hheads
        (attained_inventory_pos key levels) hK hH hvisitor)

/-- The fixed pair iterator also pays its masks, counters and final halt.
The additive ten-step term covers J=0, when there are no emitted pairs. -/
theorem pair_program_cost_le
    (k m n : ℕ) (p : CostAssembly.Resources) (P C levels K H visitor body : ℕ)
    (hmn : m ≤ n) (hbits : 1 ≤ p.bits) (hheads : 1 ≤ p.heads)
    (hKpos : 1 ≤ K) (hK : K ≤ p.labelBase ^ p.labelRows) (hH : H ≤ p.headSize)
    (hvisitor : visitor ≤ C * (levels + 1) * 2 ^ H)
    (hbody : body ≤ 2 * P * levels * K * 4 ^ H + K * visitor + 1) :
    (body + 46) * (3 * m + 1) * DifferencePairs.pairCount m (CostAssembly.jetOrder k n p) + 10 ≤
      47 * (3 * m + 1) * (2 * P + C + 1) * (levels + 1) *
        CostAssembly.assembledWork k n p ^ 2 + 10 := by
  let T := 2 * P * levels * K * 4 ^ H + K * visitor + 1
  have ht : 1 ≤ T := by dsimp [T]; omega
  have hb : body + 46 ≤ 47 * T := by change body ≤ T at hbody; omega
  have hq := pair_tuple_le_assembledWork k m n p P C levels K H visitor
    hmn hbits hheads hKpos hK hH hvisitor
  calc
    _ ≤ 47 * T * (3 * m + 1) * DifferencePairs.pairCount m (CostAssembly.jetOrder k n p) + 10 := by
      gcongr
    _ = 47 * (3 * m + 1) *
        (DifferencePairs.pairCount m (CostAssembly.jetOrder k n p) * T) + 10 := by ring
    _ ≤ 47 * (3 * m + 1) *
        ((2 * P + C + 1) * (levels + 1) * CostAssembly.assembledWork k n p ^ 2) + 10 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hq) 10
    _ = _ := by ring

/-- All new pair/traversal overhead is a fifth-degree polynomial in the
original measured budget and the retained local parameters. -/
theorem pair_program_cost_fixed_degree
    (k m n : ℕ) (p : CostAssembly.Resources) (P C levels K H visitor body : ℕ)
    (hmn : m ≤ n) (hbits : 1 ≤ p.bits) (hheads : 1 ≤ p.heads)
    (hKpos : 1 ≤ K) (hK : K ≤ p.labelBase ^ p.labelRows) (hH : H ≤ p.headSize)
    (hvisitor : visitor ≤ C * (levels + 1) * 2 ^ H)
    (hbody : body ≤ 2 * P * levels * K * 4 ^ H + K * visitor + 1) :
    (body + 46) * (3 * m + 1) * DifferencePairs.pairCount m (CostAssembly.jetOrder k n p) + 10 ≤
      500 * (CostAssembly.assembledWork k n p + m + P + C + levels + 1) ^ 5 := by
  apply (pair_program_cost_le k m n p P C levels K H visitor body hmn hbits hheads
    hKpos hK hH hvisitor hbody).trans
  let X := CostAssembly.assembledWork k n p + m + P + C + levels + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hm : 3 * m + 1 ≤ 3 * X := by dsimp [X]; omega
  have hc : 2 * P + C + 1 ≤ 3 * X := by dsimp [X]; omega
  have hl : levels + 1 ≤ X := by dsimp [X]; omega
  have hw : CostAssembly.assembledWork k n p ≤ X := by dsimp [X]; omega
  have hpow : 1 ≤ X ^ 5 := Nat.one_le_pow _ _ hX
  calc
    _ ≤ 47 * (3 * X) * (3 * X) * X * X ^ 2 + 10 := by gcongr
    _ = 423 * X ^ 5 + 10 := by ring
    _ ≤ 500 * X ^ 5 := by omega

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets
