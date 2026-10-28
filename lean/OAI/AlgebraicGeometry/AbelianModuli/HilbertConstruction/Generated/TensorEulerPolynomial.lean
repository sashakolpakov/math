import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulEulerDifference
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CommutingDifferenceAnnihilation

/-! # Tensor Euler Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.TensorEulerPolynomial

noncomputable section

/-! Two actual generated tensor factors give a polynomial for every nonnegative tensor-power Euler characteristic. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem lineBundle_eulerPolynomial_of_two_generated
    {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (L H : Line.Bundles.LineBundle X) (hH : Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators H.sheaf)
    (hLH : Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators (L.tensor H).sheaf) :
    ∃ P : Polynomial ℚ, ∀ n : ℕ,
      P.eval (n : ℚ) = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (L.tensorPower n).sheaf : ℚ) := by
  obtain ⟨r, hr⟩ := KoszulEulerDifference.lineBundleEulerShift_difference_annihilates_of_generators p H hH
  obtain ⟨s, hs⟩ := KoszulEulerDifference.lineBundleEulerShift_difference_annihilates_of_generators p (L.tensor H) hLH
  let T := LineBundle.EulerShifts.lineBundleEulerShift X (Line.Bundles.LineBundle.classOf L)
  let U := LineBundle.EulerShifts.lineBundleEulerShift X (Line.Bundles.LineBundle.classOf H)
  let v := LineBundle.EulerShifts.lineBundleClassEuler p
  have hTUv : ((T * U - 1) ^ s) v = 0 := by
    change ((LineBundle.EulerShifts.lineBundleEulerShift X (Line.Bundles.LineBundle.classOf L * Line.Bundles.LineBundle.classOf H) - 1) ^ s)
      (LineBundle.EulerShifts.lineBundleClassEuler p) = 0 at hs
    rwa [(LineBundle.EulerShifts.lineBundleEulerShift X).map_mul] at hs
  have hv := CommutingDifferenceAnnihilation.commuting_tensor_differences_annihilate T U
    (LineBundle.EulerShifts.lineBundleEulerShift_commute X (Line.Bundles.LineBundle.classOf L) (Line.Bundles.LineBundle.classOf H)) v s r hTUv hr
  let φ : (Line.Bundles.LineBundle.IsoClass X → ℤ) →+ ℤ :=
    { toFun := fun f => f 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hφ (f : Line.Bundles.LineBundle.IsoClass X → ℤ) : φ f = f 1 := rfl
  obtain ⟨P, hP⟩ := EndomorphismOrbitPolynomial.exists_polynomial_of_endomorphism_difference_annihilates T φ v (s + r) hv
  refine ⟨P, fun n => ?_⟩
  calc
    P.eval (n : ℚ) = (φ ((T ^ n) v) : ℚ) := hP n
    _ = (((T ^ n) v) 1 : ℚ) := congrArg (fun z : ℤ => (z : ℚ)) (hφ _)
    _ = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (L.tensorPower n).sheaf : ℚ) :=
      congrArg (fun z : ℤ => (z : ℚ)) (LineBundle.EulerShifts.lineBundleEulerShift_power_eval_one p L n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.TensorEulerPolynomial
