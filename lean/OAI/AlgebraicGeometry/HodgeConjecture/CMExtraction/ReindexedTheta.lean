import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.BasisTransport
import OAI.RepresentationTheory.Theta.Geometric.LinearTheta

/-! # Reindexed Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReindexedTheta.TestTransport

noncomputable section

/-! Reindexing actual finite tests, rational theta sums, and their first
derivatives. The two Siegel matrices are compared entry by entry. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Theta.Geometric.LinearTheta

variable {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J)

theorem siegelMatrixForm_reindex (M : Matrix J J ℂ) (x y : J → ℝ) :
    ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (M.submatrix e e) (fun i => x (e i)) (fun i => y (e i)) =
      ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm M x y := by
  simp only [ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply, Matrix.submatrix_apply]
  calc
    _ = ∑ i : I, ∑ j : J, (x (e i) : ℂ) * ((y j : ℂ) * M (e i) j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact e.sum_comp (fun j : J => (x (e i) : ℂ) * ((y j : ℂ) * M (e i) j))
    _ = _ := e.sum_comp (fun i : J => ∑ j : J, (x i : ℂ) * ((y j : ℂ) * M i j))

theorem reindexedThetaTerm (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (ZI : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (ZJ : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J)
    (hZ : ZI.matrix = ZJ.matrix.submatrix e e) (z : J → ℂ) (x : J → ℚ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm (Finite.BasisTransport.Test.reindexFiniteTest e φ) ZJ z x =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm φ ZI (fun i => z (e i)) (fun i => x (e i)) := by
  simp only [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm, Finite.BasisTransport.Test.reindexFiniteTest_rational, hZ]
  rw [siegelMatrixForm_reindex e ZJ.matrix (fun j => (x j : ℝ)) (fun j => (x j : ℝ)),
    e.sum_comp (fun j => (x j : ℂ) * z j)]

theorem reindexedTheta (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (ZI : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (ZJ : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J)
    (hZ : ZI.matrix = ZJ.matrix.submatrix e e) (z : J → ℂ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta (Finite.BasisTransport.Test.reindexFiniteTest e φ) ZJ z =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta φ ZI (fun i => z (e i)) := by
  unfold RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta
  simp only [reindexedThetaTerm e φ ZI ZJ hZ]
  exact (LinearEquiv.funCongrLeft ℚ ℚ e).toEquiv.tsum_eq
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm φ ZI (fun i => z (e i)))

def positionReindexLinear (R : Type*) [NontriviallyNormedField R] :
    (J → R) →L[R] (I → R) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (e i)

omit [Fintype I] [Fintype J] in
theorem positionReindexLinear_apply (R : Type*) [NontriviallyNormedField R] (x : J → R) :
    positionReindexLinear e R x = fun i => x (e i) := rfl

theorem reindexedFirst (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (ZI : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (ZJ : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J)
    (hZ : ZI.matrix = ZJ.matrix.submatrix e e) :
    RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst (Finite.BasisTransport.Test.reindexFiniteTest e φ) ZJ =
      (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ ZI).comp (positionReindexLinear e ℂ) := by
  have hzero : positionReindexLinear e ℂ (0 : J → ℂ) = 0 := map_zero _
  have hd := ((hzero.symm ▸ RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst_hasFDerivAt φ ZI).comp 0
    (positionReindexLinear e ℂ).hasFDerivAt)
  have he : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta (Finite.BasisTransport.Test.reindexFiniteTest e φ) ZJ =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta φ ZI ∘ positionReindexLinear e ℂ :=
    funext (reindexedTheta e φ ZI ZJ hZ)
  rw [← he] at hd
  exact (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst_hasFDerivAt (Finite.BasisTransport.Test.reindexFiniteTest e φ) ZJ).unique hd

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReindexedTheta.TestTransport
