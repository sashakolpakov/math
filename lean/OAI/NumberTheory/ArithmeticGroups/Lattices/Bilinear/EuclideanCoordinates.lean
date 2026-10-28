import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousBracketChange
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Euclidean Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.EuclideanCoordinates.Construction

noncomputable section

/-! Euclidean coordinates on bilinear operations record all output
coordinates of the values on pairs of basis vectors. -/

def tripleUncurryLinearEquiv (k ι : Type*) [Field k] :
    (ι → ι → ι → k) ≃ₗ[k] (ι × ι × ι → k) where
  toFun f p := f p.1 p.2.1 p.2.2
  invFun f i j l := f (i, j, l)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def bilinearNestedBasisCoordinates
    {k L ι : Type*} [Field k] [AddCommGroup L] [Module k L] [Fintype ι]
    (b : Module.Basis ι k L) : (L →ₗ[k] L →ₗ[k] L) ≃ₗ[k] (ι → ι → ι → k) :=
  (b.constr (M' := L →ₗ[k] L) k).symm.trans
    (LinearEquiv.piCongrRight fun _ => (b.constr (M' := L) k).symm.trans
      (LinearEquiv.piCongrRight fun _ => b.equivFun))

theorem bilinearNestedBasisCoordinates_apply
    {k L ι : Type*} [Field k] [AddCommGroup L] [Module k L] [Fintype ι]
    (b : Module.Basis ι k L) (B : L →ₗ[k] L →ₗ[k] L) (i j l : ι) :
    bilinearNestedBasisCoordinates b B i j l = b.equivFun (B (b i) (b j)) l := rfl

def continuousBilinearEuclideanCoordinates
    {L ι : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    [Fintype ι] (b : Module.Basis ι ℝ L) :
    (L →L[ℝ] L →L[ℝ] L) ≃L[ℝ] EuclideanSpace ℝ (ι × ι × ι) :=
  (((ContinuousBracketChange.Construction.finiteBilinearEquiv.symm.trans (bilinearNestedBasisCoordinates b)).trans
    (tripleUncurryLinearEquiv ℝ ι)).trans
    (WithLp.linearEquiv 2 ℝ (ι × ι × ι → ℝ)).symm).toContinuousLinearEquiv

theorem continuousBilinearEuclideanCoordinates_apply
    {L ι : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    [Fintype ι] (b : Module.Basis ι ℝ L) (B : L →L[ℝ] L →L[ℝ] L) (i j l : ι) :
    continuousBilinearEuclideanCoordinates b B (i, j, l) = b.equivFun (B (b i) (b j)) l := rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.EuclideanCoordinates.Construction
