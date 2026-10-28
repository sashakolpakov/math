import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AffineProductRank
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks

/-! # Ordinary Block Rank -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryBlockRank.Ordinary

noncomputable section

/-! Compute the rank of the actual ordinary block from its given
multiplicative and etale factors. This is the input to rank constancy
for an integral lift, not an additional height hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AffineProductRank

variable (k : Type) [Field k] (q n : ℕ) [NeZero q]

omit [NeZero q] in
theorem ordinaryLabels_card (d : ℕ) : Nat.card (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n d) = (q ^ n) ^ d := by
  change Nat.card (ULift (Multiplicative (Fin d → ZMod (q ^ n)))) = _
  rw [Nat.card_ulift]
  change Nat.card (Fin d → ZMod (q ^ n)) = _
  simp only [Nat.card_pi, Nat.card_zmod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem multiplicativeAlgebra_finrank (d : ℕ) :
    Module.finrank k (MonoidAlgebra k (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n d)) = (q ^ n) ^ d := by
  let := Fintype.ofFinite (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n d)
  exact (Module.finrank_eq_card_basis (MonoidAlgebra.basis (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n d) k)).trans
    (Fintype.card_eq_nat_card.trans (ordinaryLabels_card q n d))

theorem etaleAlgebra_finrank (r : ℕ) :
    Module.finrank k (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n r → k) = (q ^ n) ^ r := by
  let := Fintype.ofFinite (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n r)
  rw [Module.finrank_pi, Fintype.card_eq_nat_card]
  exact ordinaryLabels_card q n r

def ordinaryProductAffineIso (d r : ℕ) :
    (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q n d ⊗ AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.etaleOrdinaryBlock k q n r).X ≅
      AffineProductRank.affine k (MonoidAlgebra k (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n d)) ⊗
        AffineProductRank.affine k (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n r → k) :=
  tensorIso (Iso.refl _) (RepresentationTheory.Theta.Geometric.ConstantSchemeDegree.constantAffineLabelsIso k (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n r))

theorem ordinaryBlock_rank {B : Grp (Over (Spec (.of k)))} {d r : ℕ}
    (e : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k B q n d r) (z : Spec (.of k)) :
    B.X.hom.finrank z = (q ^ n) ^ (d + r) := by
  let M := MonoidAlgebra k (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n d)
  let E := AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n r → k
  have : IsFinite (AffineProductRank.affine k M).hom := AffineProductRank.affine_finite k M
  have : Flat (AffineProductRank.affine k M).hom := AffineProductRank.affine_flat k M
  have : IsFinite (AffineProductRank.affine k E).hom := AffineProductRank.affine_finite k E
  have : Flat (AffineProductRank.affine k E).hom := AffineProductRank.affine_flat k E
  have : IsFinite (AffineProductRank.affine k M ⊗ AffineProductRank.affine k E).hom :=
    inferInstanceAs (IsFinite (Limits.pullback.fst (AffineProductRank.affine k M).hom (AffineProductRank.affine k E).hom ≫ (AffineProductRank.affine k M).hom))
  have : Flat (AffineProductRank.affine k M ⊗ AffineProductRank.affine k E).hom :=
    inferInstanceAs (Flat (Limits.pullback.fst (AffineProductRank.affine k M).hom (AffineProductRank.affine k E).hom ≫ (AffineProductRank.affine k M).hom))
  let f := (Grp.forget _).mapIso e ≪≫ ordinaryProductAffineIso k q n d r
  have : IsIso f.hom.left := (Over.forget _).map_isIso f.hom
  calc
    B.X.hom.finrank z = (AffineProductRank.affine k M ⊗ AffineProductRank.affine k E).hom.finrank z := by
      erw [← f.hom.w]
      exact congrFun (Scheme.Hom.finrank_comp_left_of_isIso f.hom.left _) z
    _ = Module.finrank k M * Module.finrank k E := AffineProductRank.affine_product_rank k M E z
    _ = (q ^ n) ^ d * (q ^ n) ^ r := by
      rw [multiplicativeAlgebra_finrank, etaleAlgebra_finrank]
    _ = (q ^ n) ^ (d + r) := (pow_add _ _ _).symm

theorem ordinaryBlock_rank_three {B : Grp (Over (Spec (.of k)))} {d r : ℕ}
    (e : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k B q n d r) (hd : d + r = 3) (z : Spec (.of k)) :
    B.X.hom.finrank z = (q ^ n) ^ 3 := by
  rw [ordinaryBlock_rank k q n e z, hd]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryBlockRank.Ordinary
