import OAI.AlgebraicGeometry.GroupSchemes.FirstLevel
import OAI.AlgebraicGeometry.GroupSchemes.EtaleTower
import OAI.AlgebraicGeometry.GroupSchemes.LocalLifting

/-! # Multiplicative Levels -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! In the connected height-one case, every Cartier-dual level is split étale. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.GroupSchemes.LocalObstruction.FiniteEtale OAI.AlgebraicGeometry.GroupSchemes.Verschiebung.FiniteEtale OAI.AlgebraicGeometry.GroupSchemes.Surjective.FiniteEtaleV

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

open OAI.AlgebraicGeometry.GroupSchemes.KernelIdeal.FiniteEtale

omit [IsAlgClosed k] [Fact p.Prime] [CharP k p] in
/-- The first level cuts out the convolution p-torsion ideal at every later level. -/
theorem MultiplicativeLevels.FiniteEtale.first_iter_kernel_convolution {h : ℕ} (G : GroupSchemes.FiniteEtale.PDivisibleGroup k p h) (n : ℕ) :
    letI := (G.level (1 + n)).coordinateHopf
    letI := (G.level (1 + n)).coordinateCoalgebra
    RingHom.ker (FiniteEtale.FiniteCommGroupScheme.coordinateMap (G.inclusionIter 1 n)).toRingHom =
      LocalObstruction.FiniteEtale.multiplicationKernelIdeal k p (G.level (1 + n)).algebra := by
  let := (G.level (1 + n)).coordinateHopf
  let := (G.level (1 + n)).coordinateCoalgebra
  have he := GeometricKernel.FiniteEtale.coordinate_kernel_ideal (G.inclusionIter 1 n) p (by
    intro T x
    simpa only [pow_one] using G.inclusionIter_kernel 1 n T x)
  rw [he]
  change Ideal.span ((G.level (1 + n)).coordinatePower p ''
    (RingHom.ker (G.level (1 + n)).coordinateAugmentation.toRingHom :
      Set (G.level (1 + n)).algebra)) = _
  simp only [LocalObstruction.FiniteEtale.multiplicationKernelIdeal, LocalObstruction.FiniteEtale.augmentationIdeal,
    FiniteEtale.FiniteCommGroupScheme.coordinatePower_apply, FiniteEtale.FiniteCommGroupScheme.coordinateAugmentation]
  rfl

/-- Connected height one makes the Cartier dual of every positive level split étale. -/
theorem FiniteEtale.PDivisibleGroup.dual_split_positive_of_first_local (G : FiniteEtale.PDivisibleGroup k p 1)
    (hfirst : IsLocalRing (G.level 1).algebra) (n : ℕ) :
    Algebra.IsFiniteSplit k (G.level (1 + n)).cartierDual.algebra := by
  have hsplit1 := G.first_dual_split_of_local hfirst
  have hred1 : IsReduced (G.level 1).cartierDual.algebra :=
    Algebra.FormallyUnramified.isReduced_of_field k (G.level 1).cartierDual.algebra
  have hV1 := @Surjective.FiniteEtaleV.verschiebung_surjective k (G.level 1).algebra _ _
    (G.level 1).coordinateHopf (G.level 1).coordinateHopf_cocomm (G.level 1).finite
    p _ _ _ hred1
  have hVn := @LocalLifting.FiniteEtaleV.surjective_of_quotient
    k (G.level (1 + n)).algebra (G.level 1).algebra _ _ _
    (G.level (1 + n)).coordinateHopf (G.level 1).coordinateHopf
    (G.level (1 + n)).coordinateHopf_cocomm (G.level 1).coordinateHopf_cocomm
    (G.level (1 + n)).finite (G.level 1).finite p _ _ _
    (G.local_of_first_local hfirst (1 + n)) (FiniteEtale.FiniteCommGroupScheme.coordinateBialgMap (G.inclusionIter 1 n))
    (FiniteEtale.FiniteCommGroupScheme.coordinateMap_surjective (G.inclusionIter 1 n))
    ((MultiplicativeLevels.FiniteEtale.first_iter_kernel_convolution G n).le.trans
      (@LocalLifting.FiniteEtaleV.multiplicationKernel_le_square
        k (G.level (1 + n)).algebra _ _ (G.level (1 + n)).coordinateHopf
        (G.level (1 + n)).coordinateHopf_cocomm (G.level (1 + n)).finite p _ _ _)) hV1
  have hred : IsReduced (G.level (1 + n)).cartierDual.algebra :=
    @Surjective.FiniteEtaleV.dual_reduced_of_surjective k (G.level (1 + n)).algebra _ _
      (G.level (1 + n)).coordinateHopf (G.level (1 + n)).coordinateHopf_cocomm
      (G.level (1 + n)).finite p _ _ _ hVn
  exact FiniteAlgebra.EtaleFinite.split_of_reduced k (G.level (1 + n)).cartierDual.algebra

/-- Every Cartier-dual level is split étale in the connected height-one case. -/
theorem FiniteEtale.PDivisibleGroup.dual_split_of_first_local (G : FiniteEtale.PDivisibleGroup k p 1)
    (hfirst : IsLocalRing (G.level 1).algebra) (n : ℕ) :
    Algebra.IsFiniteSplit k (G.level n).cartierDual.algebra := by
  cases n with
  | zero =>
    apply FiniteAlgebra.EtaleFinite.split_of_rank_one
    rw [(G.level 0).cartierDual_rank, G.rank]
    simp only [Nat.zero_mul, pow_zero]
  | succ n =>
    exact (congrArg (fun m => Algebra.IsFiniteSplit k (G.level m).cartierDual.algebra)
      (Nat.add_comm 1 n)).mp (G.dual_split_positive_of_first_local hfirst n)

/-- Uniformly across an actual height-one tower, all levels are split étale,
or all their Cartier duals are split étale. -/
theorem FiniteEtale.PDivisibleGroup.all_split_or_all_dual_split (G : FiniteEtale.PDivisibleGroup k p 1) :
    (∀ n, Algebra.IsFiniteSplit k (G.level n).algebra) ∨
      (∀ n, Algebra.IsFiniteSplit k (G.level n).cartierDual.algebra) := by
  rcases G.first_local_or_split with hlocal | hsplit
  · exact Or.inr (G.dual_split_of_first_local hlocal)
  · exact Or.inl (G.split_of_first_split hsplit)

end

end OAI.AlgebraicGeometry.GroupSchemes
