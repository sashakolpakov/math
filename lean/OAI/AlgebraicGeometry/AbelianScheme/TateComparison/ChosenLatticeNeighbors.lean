import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LatticeNeighbor

/-! # Chosen Lattice Neighbors -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ChosenLatticeNeighbors

noncomputable section

/-! Forgetting the one forced scalar coordinate gives ordinary chosen
lattice neighbors, independently of the source multiplier coordinate. -/

open scoped Classical

variable (s q : ℕ) [Fact q.Prime]

abbrev ChosenLatticePoint := Fin s → Duality.RankThreeLattice ℤ_[q] ℚ_[q]

def liftLatticeNeighbor (t : Local.IntegralType s) (x : LatticeCosetConvolution.SplitLatticePoint s q)
    (M : ChosenLatticePoint s q) : LatticeCosetConvolution.SplitLatticePoint s q :=
  (M, x.2 * QuotientGroup.mk (HeckeKernel.qUnit q ^ (-t.val.multiplier)))

theorem liftLatticeNeighbor_injective (t : Local.IntegralType s) (x : LatticeCosetConvolution.SplitLatticePoint s q) :
    Function.Injective (liftLatticeNeighbor s q t x) := fun _ _ h => congrArg Prod.fst h

theorem latticeNeighborRelation_of_mem (t : Local.IntegralType s) (x y : LatticeCosetConvolution.SplitLatticePoint s q)
    (hy : y ∈ LatticeCosetConvolution.sphericalLatticeNeighbors s q t.val x) : LatticeNeighbor.LatticeNeighborRelation s q t x y := by
  have hc := Multiset.count_pos.mpr hy
  rw [LatticeNeighbor.sphericalLatticeNeighbors_count] at hc
  by_contra h
  rw [ite_eq_right h] at hc
  exact (Nat.lt_irrefl 0) hc

theorem latticeNeighbor_eq_lift (t : Local.IntegralType s) (x y : LatticeCosetConvolution.SplitLatticePoint s q)
    (hy : y ∈ LatticeCosetConvolution.sphericalLatticeNeighbors s q t.val x) : liftLatticeNeighbor s q t x y.1 = y := by
  have h := (latticeNeighborRelation_of_mem s q t x y hy).2
  apply Prod.ext
  · rfl
  change x.2 * QuotientGroup.mk (HeckeKernel.qUnit q ^ (-t.val.multiplier)) = y.2
  rw [← h, mul_inv_cancel_left]

theorem latticeNeighbors_lift_projection (t : Local.IntegralType s) (x : LatticeCosetConvolution.SplitLatticePoint s q) :
    ((LatticeCosetConvolution.sphericalLatticeNeighbors s q t.val x).map Prod.fst).map (liftLatticeNeighbor s q t x) =
      LatticeCosetConvolution.sphericalLatticeNeighbors s q t.val x := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id (LatticeCosetConvolution.sphericalLatticeNeighbors s q t.val x)]
  apply Multiset.map_congr rfl
  intro y hy
  exact latticeNeighbor_eq_lift s q t x y hy

theorem projectedLatticeNeighbors_count (t : Local.IntegralType s) (x : LatticeCosetConvolution.SplitLatticePoint s q)
    (M : ChosenLatticePoint s q) :
    ((LatticeCosetConvolution.sphericalLatticeNeighbors s q t.val x).map Prod.fst).count M =
      if ∀ i, Duality.RelativePosition (q : ℤ_[q]) (t.val.exponent i) (x.1 i) (M i) then 1 else 0 := by
  have h := congrArg (fun m => m.count (liftLatticeNeighbor s q t x M))
    (latticeNeighbors_lift_projection s q t x)
  rw [Multiset.count_map_eq_count' _ _ (liftLatticeNeighbor_injective s q t x),
    LatticeNeighbor.sphericalLatticeNeighbors_count] at h
  simpa only [LatticeNeighbor.LatticeNeighborRelation, liftLatticeNeighbor, inv_mul_cancel_left, and_true] using h

def chosenLatticeNeighbors (t : Local.IntegralType s) (L : ChosenLatticePoint s q) : Multiset (ChosenLatticePoint s q) :=
  (LatticeCosetConvolution.sphericalLatticeNeighbors s q t.val (L, 1)).map Prod.fst

theorem chosenLatticeNeighbors_count (t : Local.IntegralType s) (L M : ChosenLatticePoint s q) :
    (chosenLatticeNeighbors s q t L).count M =
      if ∀ i, Duality.RelativePosition (q : ℤ_[q]) (t.val.exponent i) (L i) (M i) then 1 else 0 :=
  projectedLatticeNeighbors_count s q t (L, 1) M

theorem projectedLatticeNeighbors_eq (t : Local.IntegralType s) (x : LatticeCosetConvolution.SplitLatticePoint s q) :
    (LatticeCosetConvolution.sphericalLatticeNeighbors s q t.val x).map Prod.fst = chosenLatticeNeighbors s q t x.1 := by
  apply Multiset.ext.mpr
  intro M
  rw [projectedLatticeNeighbors_count, chosenLatticeNeighbors_count]

theorem chosenLatticeNeighbors_convolution (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (u v : Local.IntegralType s) (L : ChosenLatticePoint s q) :
    (chosenLatticeNeighbors s q u L).bind (chosenLatticeNeighbors s q v) =
      (ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum (fun w n => n • chosenLatticeNeighbors s q w L) := by
  have h := congrArg (LatticeCosetConvolution.multisetMapHom (Prod.fst : LatticeCosetConvolution.SplitLatticePoint s q → ChosenLatticePoint s q))
    (LatticeCosetConvolution.sphericalLatticeNeighbors_convolution s q hElementaryDivisors u v (L, 1))
  change ((LatticeCosetConvolution.sphericalLatticeNeighbors s q u.val (L, 1)).bind (LatticeCosetConvolution.sphericalLatticeNeighbors s q v.val)).map Prod.fst = _ at h
  rw [Multiset.map_bind] at h
  simp only [projectedLatticeNeighbors_eq, map_finsuppSum, map_nsmul] at h
  change ((LatticeCosetConvolution.sphericalLatticeNeighbors s q u.val (L, 1)).map Prod.fst).bind (chosenLatticeNeighbors s q v) = _
  rw [Multiset.bind_map]
  exact h

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ChosenLatticeNeighbors
