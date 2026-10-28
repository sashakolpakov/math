import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix

namespace OAI.Algorithms

/-! Natural-address interface for the produced row-major matrix. Row indices
are incidence-plan positions; columns are the emitted original variable IDs. -/
namespace SubexponentialSAT.SqrtLog.LayoutProducedMatrix
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutExactBuckets LayoutProgram

variable {r Q D N : ℕ} {O : Type*} [CommRing O] {node : Fin Q → O}

def literalNat (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin N) (A R : ℕ) (t : Fin Q) (j v : ℕ) : ℤ :=
  if hj : j < D then if hv : v < N then
    literalMatrix P owner A R t ⟨j,hj⟩ ⟨v,hv⟩ else 0 else 0

@[simp] theorem literalNat_fin (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin N) (A R : ℕ) (t : Fin Q) (j : Fin D) (v : Fin N) :
    literalNat P owner A R t j.val v.val=literalMatrix P owner A R t j v := by
  simp [literalNat]

theorem selected_nat_rank_le
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin N)
    (head : Fin Q → Fin N → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r)
    (js : List ℕ) (hjs : ∀ v∈js,v < N)
    (hjshead : ∀ v (hv : v∈js),head t ⟨v,hjs v hv⟩=g) :
    LayoutRank.rowRank (fun (j : Fin D) (i : Fin js.length)=>
      literalNat P owner A R t j.val (js.get i)) ≤
    LayoutRank.rowRank (pulledConstraints (headOwner P owner head hhead t g)
      (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g)) := by
  let selected : Fin js.length → {v : Fin N // head t v=g} := fun i=>
    ⟨⟨js.get i,hjs _ (List.get_mem ..)⟩,hjshead _ (List.get_mem ..)⟩
  have h := selected_literal_rank_le P owner head hhead A R denom hdenom units t g selected
  convert h using 1
  congr 1
  funext j i
  have hi : js.get i < N := hjs _ (List.get_mem ..)
  change literalNat P owner A R t j.val (js.get i) =
    literalMatrix P owner A R t j ⟨js.get i,hi⟩
  unfold literalNat
  rw [dite_eq_left j.isLt,dite_eq_left hi]

/-- Canonical pulled constraints summed over the actual variable heads. The
factor labels do not enter this rank statement. -/
theorem canonical_total_rank_le
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin N)
    (head : Fin Q → Fin N → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q)
    (ε : ℚ) (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4*R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q-1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ)^2)
    (hcover : (1-ε)*(D:ℚ) ≤ P.blockCount*(Fintype.card (UniversalType r Q 1):ℚ)) :
    (∑ g : Fin r,(LayoutRank.rowRank (pulledConstraints
      (headOwner P owner head hhead t g)
      (LayoutBlocks.constraints (LayoutUniversal.data
        (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R denom hdenom units)
        P.completeBlocks t g)) : ℚ)) ≤ 2*ε*D := by
  let C := LayoutUniversal.data (r := r)
    (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R denom hdenom units
  have h := LayoutRank.blocks_data_total_rank_le C P.completeBlocks
    (id : Fin D → Fin D) (fun i t=>(P.label i).slot 0 t) (by intros; rfl)
    t ε hε.le (LayoutRank.universal_total_rank_le R denom hdenom units t
      ε hr hQ hR hsize hε hwidth) (by simpa using hcover)
  have hblocks :
    (∑ g : Fin r,(LayoutRank.rowRank (LayoutBlocks.constraints C P.completeBlocks t g) : ℚ))
      ≤ 2*ε*D := by
    calc
      _ = ∑ g : Fin r, (LayoutRank.rowRank
          ((LayoutBlocks.data C P.completeBlocks (id : Fin D → Fin D)
            (fun i t => (P.label i).slot 0 t) (by intros; rfl)).constraints t g) : ℚ) := by
            apply Finset.sum_congr rfl
            intro g _
            exact_mod_cast (LayoutRank.blocks_data_rank_eq C P.completeBlocks
              (id : Fin D → Fin D) (fun i t => (P.label i).slot 0 t)
              (by intros; rfl) t g).symm
      _ ≤ 2 * ε * D := by simpa only [Fintype.card_fin] using h
  apply le_trans _ hblocks
  apply Finset.sum_le_sum
  intro g _
  exact_mod_cast LayoutRank.rowRank_pullback_le (headOwner P owner head hhead t g)
    (LayoutBlocks.constraints C P.completeBlocks t g)

theorem selected_nat_total_rank_le
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin N)
    (head : Fin Q → Fin N → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q)
    (js : Fin r → List ℕ) (hjs : ∀ g v,v∈js g→v < N)
    (hjshead : ∀ g v (hv : v∈js g),head t ⟨v,hjs g v hv⟩=g)
    (ε : ℚ) (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4*R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q-1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ)^2)
    (hcover : (1-ε)*(D:ℚ) ≤ P.blockCount*(Fintype.card (UniversalType r Q 1):ℚ)) :
    (∑ g : Fin r,(LayoutRank.rowRank (fun (j : Fin D) (i : Fin (js g).length)=>
      literalNat P owner (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R t
        j.val ((js g).get i)) : ℚ)) ≤ 2*ε*D := by
  apply le_trans _ (canonical_total_rank_le P owner head hhead R denom hdenom units t
    ε hr hQ hR hsize hε hwidth hcover)
  apply Finset.sum_le_sum
  intro g _
  exact_mod_cast selected_nat_rank_le P owner head hhead
    (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R denom hdenom units t g
    (js g) (hjs g) (hjshead g)

end SubexponentialSAT.SqrtLog.LayoutProducedMatrix

end OAI.Algorithms
