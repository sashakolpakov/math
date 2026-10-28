import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramProducedRankLiteral
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramSemantics

namespace OAI.Algorithms

/-! The actual produced matrices, attained head tables and Cartesian inventory
share one proof-only maximum rank. Selection is in the emitted original-ID
order, and the canonical rank bound is discharged by literal pullback. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LeafHeadSetupProgram

variable {r Q D n : ℕ}

def actualRank (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R : ℕ) (rows : List (List Bool)) (low : List Bool)
    (t : Fin Q) (g : Fin r) : ℕ :=
  headRank (LayoutProducedMatrix.literalNat P owner A R t) D n rows low (t.val*r+g.val)

theorem fiber_product_le_maxTotalRank {base : Data} {N B : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R : ℕ) (t : Fin Q)
    (ps : Fin D → ℕ × ℕ) (hp : ∀ i,(ps i).1=(owner i).val) (H : ℕ)
    {tables : List BucketTupleProgram.HeadTable}
    (ht : ProducedHeads base n N D rows low
      (FiberRel (List.ofFn ps) (entryNat P A R t) H) B (t.val*r) tables)
    (hlen : tables.length=r) (hW : H ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141))
    (nodes : Finset (Fin Q)) (htmem : t∈nodes) :
    (tables.map fun table=>table.buckets.length).prod ≤ (commonBase n H)^
      CostAssembly.maxTotalRank nodes (actualRank P owner A R rows low) := by
  apply CostAssembly.inventory_le_maxTotalRank _ _ nodes _ (commonBase_pos n H) htmem
  exact producedHeads_fiber_product P owner A R t ps hp H ht hlen hW

theorem fiber_enumerate_le_maxTotalRank {base : Data} {N B : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R : ℕ) (t : Fin Q)
    (ps : Fin D → ℕ × ℕ) (hp : ∀ i,(ps i).1=(owner i).val) (H : ℕ)
    {tables : List BucketTupleProgram.HeadTable}
    (ht : ProducedHeads base n N D rows low
      (FiberRel (List.ofFn ps) (entryNat P A R t) H) B (t.val*r) tables)
    (hlen : tables.length=r) (hW : H ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141))
    (nodes : Finset (Fin Q)) (htmem : t∈nodes) :
    (BucketTupleProgram.enumerate tables).length ≤ (commonBase n H)^
      CostAssembly.maxTotalRank nodes (actualRank P owner A R rows low) := by
  rw [BucketTupleProgram.enumerate_length]
  exact fiber_product_le_maxTotalRank P owner A R t ps hp H ht hlen hW nodes htmem

/-- The produced Cartesian inventory fits the assembled numerical resource
once labelBase and labelRows contain the proved common base and maximum. -/
theorem fiber_product_le_assembledWork {base : Data} {N B : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R : ℕ) (t : Fin Q)
    (ps : Fin D → ℕ × ℕ) (hp : ∀ i,(ps i).1=(owner i).val) (H k m : ℕ)
    {tables : List BucketTupleProgram.HeadTable}
    (ht : ProducedHeads base n N D rows low
      (FiberRel (List.ofFn ps) (entryNat P A R t) H) B (t.val*r) tables)
    (hlen : tables.length=r) (hW : H ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141))
    (nodes : Finset (Fin Q)) (htmem : t∈nodes) (p : CostAssembly.Resources)
    (hbase : commonBase n H ≤ p.labelBase)
    (hrank : CostAssembly.maxTotalRank nodes (actualRank P owner A R rows low) ≤ p.labelRows)
    (hheads : 1 ≤ p.heads) (hbits : 1 ≤ p.bits) :
    (tables.map fun table=>table.buckets.length).prod ≤ CostAssembly.assembledWork k m p := by
  apply CostAssembly.labelInventory_le_assembledWork k m p _ _ hheads hbits
  apply (fiber_product_le_maxTotalRank P owner A R t ps hp H ht hlen hW nodes htmem).trans
  exact (Nat.pow_le_pow_left hbase _).trans
    (Nat.pow_le_pow_right ((commonBase_pos n H).trans hbase) hrank)

theorem actualRank_sum_le {O : Type*} [CommRing O] {node : Fin Q → O}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (R : ℕ) (denom : Oˣ) (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q)
    (rows : List (List Bool)) (low : List Bool)
    (hselected : ∀ (g : Fin r) (v : Fin n),v.val∈selectedHeads n rows low (t.val*r+g.val)→head t v=g)
    (ε : ℚ) (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4*R ≤ Q) (hε : 0 < ε)
    (hwidth : 32*((Q-1 : ℕ):ℝ)*Real.log (2 / (ε:ℝ)) ≤ (R:ℝ)^2)
    (hcover : (1-ε)*(D:ℚ) ≤ P.blockCount*(Fintype.card (UniversalType r Q 1):ℚ)) :
    (∑ g : Fin r,(actualRank P owner (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R)
      R rows low t g : ℚ)) ≤ 2*ε*D := by
  exact LayoutProducedMatrix.selected_nat_total_rank_le P owner head hhead R denom hdenom units t
    (fun g=>selectedHeads n rows low (t.val*r+g.val))
    (fun g=>HeadIdentifierProgram.chosenIds_bound _ n)
    (fun g v hv=>hselected g ⟨v,HeadIdentifierProgram.chosenIds_bound _ n v hv⟩ hv)
    ε hr hQ hR hsize hε hwidth hcover

/-- The membership premise above is discharged by the actual assignment
controller output, rather than an assumed head table or permutation. -/
theorem source_selected_head {N : ℕ}
    (owner : Fin D → Fin n) (factor : Fin D → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm (Fin D) (Fin n) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator) (low : Fin n → Bool)
    (t : Fin Q) (g : Fin r) (v : Fin n)
    (hv : v.val∈selectedHeads n (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits low) (t.val*r+g.val)) :
    Packing.computedWords owner factor a tail terms
      (LeafHeadFactorsProgram.indices n N) x y (.inl v) t=g :=
  ((selectedHeads_source_mem owner factor a tail terms w x y hy hx low t g v).mp hv).2

/-- Specialization to the literal assignment-controller table. This discharges
all selected-head membership and ordering obligations from the checked source
semantics, including the low-variable filter. -/
theorem source_actualRank_sum_le {N : ℕ} {O : Type*} [CommRing O] {node : Fin Q → O}
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (factor : Fin D → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm (Fin D) (Fin n) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator) (low : Fin n → Bool)
    (hhead : ∀ i t,(P.label i).head t=Packing.computedWords owner factor a tail terms
      (LeafHeadFactorsProgram.indices n N) x y (.inl (owner i)) t)
    (R : ℕ) (denom : Oˣ) (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q)
    (ε : ℚ) (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4*R ≤ Q) (hε : 0 < ε)
    (hwidth : 32*((Q-1 : ℕ):ℝ)*Real.log (2 / (ε:ℝ)) ≤ (R:ℝ)^2)
    (hcover : (1-ε)*(D:ℚ) ≤ P.blockCount*(Fintype.card (UniversalType r Q 1):ℚ)) :
    (∑ g : Fin r,(actualRank P owner (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R
      (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits low) t g : ℚ)) ≤ 2*ε*D := by
  apply actualRank_sum_le P owner
    (fun t v=>Packing.computedWords owner factor a tail terms
      (LeafHeadFactorsProgram.indices n N) x y (.inl v) t)
    hhead R denom hdenom units t _ _ _ ε hr hQ hR hsize hε hwidth hcover
  intro g v hv
  exact source_selected_head owner factor a tail terms w x y hy hx low t g v hv

/-- The finite maximum of the actual matrix ranks satisfies the scheduled
resource budget. It is independent of the full row count retained on tape. -/
theorem actualMax_rank_budget {O : Type*} [CommRing O] {node : Fin Q → O}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (R : ℕ) (denom : Oˣ) (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (rows : List (List Bool)) (low : List Bool) (nodes : Finset (Fin Q))
    (hselected : ∀ t∈nodes,∀ (g : Fin r) (v : Fin n),
      v.val∈selectedHeads n rows low (t.val*r+g.val)→head t v=g)
    (m B : ℕ) (hB : 0 < B) (hD : D ≤ B*m)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4*R ≤ Q)
    (hε : 0 < Asymptotic.layoutEpsilon m B)
    (hwidth : 32*((Q-1 : ℕ):ℝ)*Real.log (2 / (Asymptotic.layoutEpsilon m B:ℝ)) ≤ (R:ℝ)^2)
    (hcover : (1-Asymptotic.layoutEpsilon m B)*(D:ℚ) ≤
      P.blockCount*(Fintype.card (UniversalType r Q 1):ℚ)) :
    16 * (Asymptotic.layoutR m : ℝ) * (Asymptotic.L m : ℝ)^2 *
      (CostAssembly.maxTotalRank nodes (actualRank P owner
        (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R rows low) : ℝ) ≤ (m : ℝ) := by
  apply CostAssembly.scheduled_maxTotalRank_le_real nodes m B (fun _=>D)
    (actualRank P owner (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R rows low)
    hB (fun _ _=>hD)
  intro t ht
  exact actualRank_sum_le P owner head hhead R denom hdenom units t rows low
    (hselected t ht) (Asymptotic.layoutEpsilon m B) hr hQ hR hsize hε hwidth hcover

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end
end OAI.Algorithms
