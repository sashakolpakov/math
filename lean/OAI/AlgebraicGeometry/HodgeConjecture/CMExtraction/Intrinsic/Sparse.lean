import OAI.RepresentationTheory.Theta.CosetTests
import OAI.RepresentationTheory.Theta.CosetPoisson
import OAI.AlgebraicGeometry.ComplexMultiplication.ThetaCompletion

/-! # Sparse -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Sparse

noncomputable section

/-! Sparse integral cosets as genuine native finite-adelic Schwartz tests. -/

open scoped Classical
open OAI.AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM

variable {ι : Type*} [Fintype ι]

def latticeRational (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) : ι → ℚ :=
  fun i => ((RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerLatticeEquiv (ι := ι)).symm a i : ℚ)

theorem latticeRational_real (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (i : ι) :
    (latticeRational a i : ℝ) = a.val i := by
  have h := congrFun (congrArg Subtype.val ((RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerLatticeEquiv (ι := ι)).apply_symm_apply a)) i
  simpa only [latticeRational, Rat.cast_intCast, RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerLatticeEquiv_apply, RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerReal] using h

theorem latticeRational_injective : Function.Injective (latticeRational (ι := ι)) := by
  intro a b h
  apply Subtype.ext
  funext i
  rw [← latticeRational_real a i, ← latticeRational_real b i, h]

theorem latticeRational_grid (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (n : ℕ) (m : ι → ℤ) :
    latticeRational (a + (n + 1) • RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerLatticeEquiv m) =
      RepresentationTheory.Theta.CosetPoisson.AutomorphyConstruction.rationalGrid (n + 1 : ℚ) (latticeRational a) m := by
  funext i
  apply Rat.cast_injective (α := ℝ)
  simp [latticeRational_real, RepresentationTheory.Theta.CosetPoisson.AutomorphyConstruction.rationalGrid, RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerLatticeEquiv_apply, RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerReal,
    nsmul_eq_mul]

theorem sparse_rational_coset_iff (a x : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (n : ℕ) :
    (∃ m : ι → ℤ, RepresentationTheory.Theta.CosetPoisson.AutomorphyConstruction.rationalGrid (n + 1 : ℚ) (latticeRational a) m = latticeRational x) ↔
      ComplexMultiplication.SparseLatticeSums.CM.SparseLatticeCoset (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) n a x := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerLatticeEquiv m,
      latticeRational_injective (hm.symm.trans (latticeRational_grid a n m).symm)⟩
  · rintro ⟨y, rfl⟩
    refine ⟨RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerLatticeEquiv.symm y, ?_⟩
    rw [← latticeRational_grid, RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerLatticeEquiv.apply_symm_apply]

def nativeSparseTest (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (n : ℕ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι :=
  RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest (n + 1 : ℚ) (by exact_mod_cast Nat.succ_ne_zero n)
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (latticeRational a))

theorem nativeSparseTest_lattice_value (a x : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (n : ℕ) :
    (nativeSparseTest a n).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (latticeRational x)) =
      if ComplexMultiplication.SparseLatticeSums.CM.SparseLatticeCoset (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) n a x then 1 else 0 := by
  have hmem := (RepresentationTheory.Theta.CosetPoisson.AutomorphyConstruction.rational_finiteCoset_mem_iff (n + 1 : ℚ)
    (by exact_mod_cast Nat.succ_ne_zero n) (latticeRational a) (latticeRational x)).trans
      (sparse_rational_coset_iff a x n)
  simp only [nativeSparseTest, RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest_apply, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator,
    Set.indicator_apply, SetLike.mem_coe, hmem]

theorem nativeSparseTest_support (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (n : ℕ) (x : ι → ℚ)
    (hx : (nativeSparseTest a n).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x) ≠ 0) :
    x ∈ Set.range (latticeRational (ι := ι)) := by
  have hm : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x - RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (latticeRational a) ∈
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (n + 1 : ℚ) (by exact_mod_cast Nat.succ_ne_zero n) := by
    by_contra h
    exact hx (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_notMem _ _ h)
  obtain ⟨m, hm⟩ := (RepresentationTheory.Theta.CosetPoisson.AutomorphyConstruction.rational_finiteCoset_mem_iff _ _ _ _).mp hm
  exact ⟨a + (n + 1) • RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerLatticeEquiv m, (latticeRational_grid a n m).trans hm⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Sparse
