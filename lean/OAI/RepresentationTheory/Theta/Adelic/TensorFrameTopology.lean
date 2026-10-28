import OAI.RepresentationTheory.Theta.Adelic.IntegralFrameCoordinates
import OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology

/-! # Tensor Frame Topology -/

namespace OAI.RepresentationTheory.Theta.Adelic.TensorFrameTopology

noncomputable section

/-! Continuity of an arbitrary native quadratic tensor frame and its
inverse, for the actual coefficient topology on the quadratic algebra. -/

open scoped Classical

open OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction OAI.RepresentationTheory.Theta.Adelic.IntegralFrameCoordinates

instance quadraticContinuousSMul {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (d : R) : ContinuousSMul R (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d) where
  continuous_smul := by
    rw [Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
    exact ⟨continuous_fst.mul ((Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re d).comp continuous_snd),
      continuous_fst.mul ((Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im d).comp continuous_snd)⟩

variable {k I J : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (d : k)

omit [Fintype J] [DecidableEq J] in
theorem linear_coordinates_continuous (L : (I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) →ₗ[k] (J → k)) :
    Continuous L := by
  have he (x : I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) : L x =
      (∑ i, (x i).re • L (Pi.single i 1)) +
        ∑ i, (x i).im • L (Pi.single i (Weil.AdelicSplitting.Integral.Construction.quadraticGenerator d)) := by
    have h := congrArg L (IntegralFrameCoordinates.quadratic_vector_expansion d x)
    simpa only [map_add, map_sum, map_smul] using h
  have hc : Continuous (fun x : I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d =>
      (∑ i, (x i).re • L (Pi.single i 1)) +
        ∑ i, (x i).im • L (Pi.single i (Weil.AdelicSplitting.Integral.Construction.quadraticGenerator d))) :=
    (continuous_finsetSum _ (fun i _ =>
      ((Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re d).comp (continuous_apply i)).smul continuous_const)).add
      (continuous_finsetSum _ (fun i _ =>
        ((Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im d).comp (continuous_apply i)).smul continuous_const))
  exact hc.congr (fun x => (he x).symm)

omit [Fintype I] [DecidableEq I] in
theorem inverse_coordinates_continuous (L : (J → k) →ₗ[k] (I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) :
    Continuous L := by
  have he (x : J → k) : L x = ∑ j, x j • L (Pi.single j 1) := by
    have h := congrArg L ((Pi.basisFun k J).sum_repr x)
    simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply] using h.symm
  have hc : Continuous (fun x : J → k => ∑ j, x j • L (Pi.single j 1)) :=
    continuous_finsetSum _ (fun j _ => (continuous_apply j).smul continuous_const)
  exact hc.congr (fun x => (he x).symm)

theorem frame_continuous {n m : ℕ}
    {H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)}
    {K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)} (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K) :
    Continuous P.coordinates := linear_coordinates_continuous d P.coordinates.toLinearMap

theorem frame_inverse_continuous {n m : ℕ}
    {H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)}
    {K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)} (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K) :
    Continuous P.coordinates.symm := inverse_coordinates_continuous d P.coordinates.symm.toLinearMap

end

end OAI.RepresentationTheory.Theta.Adelic.TensorFrameTopology
