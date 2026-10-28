import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateBlockBasis
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateFiniteness

/-! # Block Coordinates -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.BlockCoordinates

noncomputable section

/-! Construct higher-level coordinates of the actual geometric CMPoints
block from its q-torsion point count. Geometric division and finiteness
come from TorsionQuotient, and the coordinate equivalence uses the original block
inclusion rather than a separately specified group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E L : Type} [Field E] [NumberField E] [IsGalois ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  {K : Type} [Field K] [CharZero K] {S : Scheme} (base : S ⟶ Spec (.of K))
  {g N : ℕ} (F : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
  (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
  (τ : Gal(E/ℚ))

abbrev originalGeometricBlock (n : ℕ) :=
  Additive (Over.mk b ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n)
    ((AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n τ)))

variable (hcard : Nat.card (originalGeometricBlock j iota hsplit F k b τ 1) = q ^ 3)

include hcard in
omit [IsAlgClosed k] in
theorem geometricFiniteTateBlock_card :
    Nat.card (AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks.Construction.l45FiniteTateBlock j iota hsplit (Over.mk b) F 1 τ) = q ^ 3 :=
  (Nat.card_congr (AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks.Construction.l45TateNativeBlockEquiv j iota hsplit (Over.mk b) F 1 τ).toEquiv).trans hcard

def geometricIntegralBlockBasis :
    Module.Basis (Fin 3) ℤ_[q] (AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks.Construction.l45IntegralTateBlock j iota hsplit (Over.mk b) F τ) := by
  have := AbelianScheme.IsogenyQuotient.Geometric.TateFiniteness.Construction.geometricTorsion_finite_from_TorsionQuotient base F.abelian k b q 1
  exact AbelianScheme.IsogenyQuotient.TateBlockBasis.Construction.rankThreeTateBlockBasis q
    (AbelianScheme.IsogenyQuotient.Geometric.TateKernel.Construction.geometricPoint_q_divisible_from_TorsionQuotient base F.abelian b q Fact.out AbelianScheme.IsogenyQuotient.Torsion.Construction.verified_TorsionQuotientInput)
    (AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks.Construction.l45SplitTateAction j iota hsplit (Over.mk b) F) τ
    (AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks.Construction.l45SplitTorsionAction j iota hsplit (Over.mk b) F 1)
    (AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks.Construction.l45Evaluate_splitAction j iota hsplit (Over.mk b) F 1)
    (geometricFiniteTateBlock_card j iota hsplit F k b τ hcard)

def geometricBlockCoordinates (n : ℕ) :
    originalGeometricBlock j iota hsplit F k b τ n ≃+ (Fin 3 → ZMod (q ^ n)) :=
  (AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks.Construction.l45TateNativeBlockEquiv j iota hsplit (Over.mk b) F n τ).symm.trans
    (AbelianScheme.IsogenyQuotient.BlockTateCoordinates.Construction.blockTateTorsionCoordinates q n
      (AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks.Construction.l45SplitTateAction j iota hsplit (Over.mk b) F)
      (AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks.Construction.l45SplitTorsionAction j iota hsplit (Over.mk b) F n)
      (AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks.Construction.l45Evaluate_splitAction j iota hsplit (Over.mk b) F n)
      (AbelianScheme.IsogenyQuotient.Geometric.TateKernel.Construction.geometricPoint_q_divisible_from_TorsionQuotient base F.abelian b q Fact.out AbelianScheme.IsogenyQuotient.Torsion.Construction.verified_TorsionQuotientInput) τ
      (geometricIntegralBlockBasis j iota hsplit base F k b τ hcard))

include hcard base in
theorem originalGeometricBlock_card (n : ℕ) :
    Nat.card (originalGeometricBlock j iota hsplit F k b τ n) = (q ^ n) ^ 3 := by
  have h := Nat.card_congr
    (geometricBlockCoordinates j iota hsplit base F k b τ hcard n).toEquiv
  simpa only [Nat.card_pi, Nat.card_zmod, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using h

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.BlockCoordinates
