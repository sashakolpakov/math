import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Sparse
import OAI.RepresentationTheory.Theta.Geometric.LinearTheta

/-! # Sparse First -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SparseFirst

noncomputable section

section

/-! Native PoissonAutomorphy theta derivatives span, using actual sparse coset tests. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Theta.Geometric.LinearTheta

variable {ι : Type*} [Fintype ι]

theorem nativeTheta_sparseTest (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (n : ℕ)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta (Sparse.nativeSparseTest a n) Z z =
      Z.phase.thetaSeriesOn (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι)
        {x | ComplexMultiplication.SparseLatticeSums.CM.SparseLatticeCoset (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) n a x} z := by
  unfold RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta
  rw [← Sparse.latticeRational_injective.tsum_eq
    (show Function.support (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm (Sparse.nativeSparseTest a n) Z z) ⊆
      Set.range (Sparse.latticeRational (ι := ι)) from ?_)]
  · apply tsum_congr
    intro x
    simp only [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm, Sparse.nativeSparseTest_lattice_value, Sparse.latticeRational_real,
      ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTermOn, Set.mem_ofPred_eq]
    split_ifs
    · simp only [one_mul, ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTerm, ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase,
        ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply]
      congr 1
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have h := congrArg (fun r : ℝ => (r : ℂ)) (Sparse.latticeRational_real x i)
      simpa using congrArg (fun c : ℂ => c * z i) h
    · simp
  · intro x hx
    apply Sparse.nativeSparseTest_support a n x
    intro hzero
    exact hx (by simp [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm, hzero])

theorem nativeSparseTest_first (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (n : ℕ)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst (Sparse.nativeSparseTest a n) Z =
      Z.phase.sparseThetaGradient (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) (ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) a n := by
  have hraw := funext (nativeTheta_sparseTest a n Z)
  have hd := RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst_hasFDerivAt (Sparse.nativeSparseTest a n) Z
  rw [hraw] at hd
  exact hd.fderiv.symm

theorem nativeFirstTheta_surjective (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    Function.Surjective (RepresentationTheory.Theta.Geometric.LinearTheta.firstThetaLinear Z) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← Z.span_sparseThetaGradients_eq_top]
  apply Submodule.span_le.mpr
  rintro l ⟨⟨a, n⟩, rfl⟩
  exact ⟨Sparse.nativeSparseTest a n, nativeSparseTest_first a n Z⟩

end

section

/-! Cotangent spanning already holds for finite linear combinations of
the explicit integral sparse tests, before choosing the good prime. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.Geometric.LinearTheta

variable {ι : Type*} [Fintype ι]

def nativeSparseInputs : Submodule ℂ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) :=
  Submodule.span ℂ (Set.range (fun an : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι × ℕ =>
    Sparse.nativeSparseTest an.1 an.2))

theorem nativeSparseInputs_image (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    Submodule.map (RepresentationTheory.Theta.Geometric.LinearTheta.firstThetaLinear Z) nativeSparseInputs = ⊤ := by
  apply top_unique
  rw [← Z.span_sparseThetaGradients_eq_top]
  apply Submodule.span_le.mpr
  rintro l ⟨⟨a, n⟩, rfl⟩
  exact ⟨Sparse.nativeSparseTest a n, Submodule.subset_span ⟨(a, n), rfl⟩,
    nativeSparseTest_first a n Z⟩

theorem exists_nativeSparseInput_first (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (l : (ι → ℂ) →L[ℂ] ℂ) :
    ∃ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι, φ ∈ nativeSparseInputs ∧ RepresentationTheory.Theta.Geometric.LinearTheta.firstThetaLinear Z φ = l := by
  have h : l ∈ Submodule.map (RepresentationTheory.Theta.Geometric.LinearTheta.firstThetaLinear Z) nativeSparseInputs := by
    rw [nativeSparseInputs_image]
    trivial
  exact h

end

/-! The spanning sparse tests have integral finite support and a positive
integer translation level, all chosen before the good prime. -/

open scoped Classical

variable {ι : Type*} [Fintype ι]

def integralSupportedTests : Submodule ℂ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) where
  carrier := {φ | ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0}
  zero_mem' _ _ := rfl
  add_mem' {f g} hf hg x hx := by
    change f.val x + g.val x = 0
    rw [hf x hx, hg x hx, add_zero]
  smul_mem' c φ hφ x hx := by
    change c * φ.val x = 0
    rw [hφ x hx, mul_zero]

theorem nativeSparseTest_integral_supported (a : ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (n : ℕ) :
    Sparse.nativeSparseTest a n ∈ integralSupportedTests := by
  have ha : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (Sparse.latticeRational a) ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors := by
    intro i
    exact (RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.rational_integral_iff (Sparse.latticeRational a i)).mpr ⟨RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction.integerLatticeEquiv.symm a i, rfl⟩
  intro x hx
  apply RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_notMem
  intro h
  have h' : x - RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (Sparse.latticeRational a) ∈
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice ((n + 1 : ℕ) : ℚ) (by exact_mod_cast (Nat.succ_pos n).ne') := by
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hi := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.add_mem
    (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_nat_subset_integral (n + 1) (Nat.succ_pos n) h') ha
  exact hx (by simpa only [sub_add_cancel] using hi)

theorem nativeSparseInputs_integral_supported :
    nativeSparseInputs (ι := ι) ≤ integralSupportedTests := by
  apply Submodule.span_le.mpr
  rintro φ ⟨⟨a, n⟩, rfl⟩
  exact nativeSparseTest_integral_supported a n

theorem nativeSparseInput_level (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (hφ : φ ∈ nativeSparseInputs) :
    (∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0) ∧
      ∃ N : ℕ, ∃ hN : 0 < N,
        ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'), ∀ x, φ.val (u + x) = φ.val x :=
  ⟨nativeSparseInputs_integral_supported hφ, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_lattice_period φ⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SparseFirst
