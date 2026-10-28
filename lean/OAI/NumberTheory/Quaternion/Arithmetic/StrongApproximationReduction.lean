import OAI.NumberTheory.Quaternion.Arithmetic.MatrixApproximation
import OAI.NumberTheory.Quaternion.Arithmetic.ExceptionalApproximation
import OAI.NumberTheory.Quaternion.Arithmetic.AdelicPolynomialCurves
import OAI.NumberTheory.Quaternion.Arithmetic.GeometricStructure

/-! # Strong Approximation Reduction -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.StrongApproximationReduction

noncomputable section

/-! In the quaternion case, finite-place weak approximation and
local additive generation are proved. The remaining input to this
strong-approximation reduction is arithmetic quotient volume. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Filter Set

variable {F : Type} [Field F] [NumberField F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
  (S : Finset (LocalAdeles.Place F)) (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S)

include ha hb harch

theorem quaternion_selected_weakApproximation (B : Finset (ApproximationTopology.AwayPlace S)) :
    DenseRange (fun g : (MatrixGroup.quaternionNormOneMatrixGroup a b).RationalPoints =>
      fun w : (B : Set (ApproximationTopology.AwayPlace S)) => LocalAdeles.diagonalLocal (MatrixGroup.quaternionNormOneMatrixGroup a b) w.val.val g) := by
  let G := MatrixGroup.quaternionNormOneMatrixGroup a b
  let e := SelectedArithmeticProduct.selectedFiniteProductEquiv G S B harch
  have hd := MatrixApproximation.denseRange_quaternionMatrix_finite_projection (SelectedArithmeticProduct.selectedFinitePlaces S B harch) a b
    (SelectedArithmeticProduct.selectedFinitePlaces_injective S B harch) ha hb
  have hcomp := e.symm.surjective.denseRange.comp hd e.symm.continuous
  have he : e.symm ∘ Product.diagonalFiniteProduct G (SelectedArithmeticProduct.selectedFinitePlaces S B harch) =
      (fun g : G.RationalPoints => fun w : (B : Set (ApproximationTopology.AwayPlace S)) => LocalAdeles.diagonalLocal G w.val.val g) := by
    funext g
    apply e.injective
    rw [Function.comp_apply, ContinuousMulEquiv.apply_symm_apply]
    funext w
    exact (SelectedArithmeticProduct.localPointsPlaceEquiv_diagonal G (SelectedArithmeticProduct.inr_awayFinitePlace S harch w.val).symm g).symm
  rw [he] at hcomp
  exact hcomp

theorem quaternion_exists_exceptional_places :
    ∃ B : Finset (ApproximationTopology.AwayPlace S), ∀ w : ApproximationTopology.AwayPlace S, w ∉ B →
      ExceptionalApproximation.localAdditiveGeneration (MatrixGroup.quaternionNormOneMatrixGroup a b) w.val := by
  have he := (AdelicPolynomialCurves.awayFinitePlace_injective S harch).tendsto_cofinite
    (MatrixApproximation.eventually_quaternionMatrix_local_additive_generation a b ha hb)
  have hg : ∀ᶠ w : ApproximationTopology.AwayPlace S in cofinite,
      ExceptionalApproximation.localAdditiveGeneration (MatrixGroup.quaternionNormOneMatrixGroup a b) w.val := by
    filter_upwards [he] with w hw
    change ExceptionalApproximation.localAdditiveGeneration (MatrixGroup.quaternionNormOneMatrixGroup a b)
      (.inr (SelectedArithmeticProduct.awayFinitePlace S harch w)) at hw
    simpa only [SelectedArithmeticProduct.inr_awayFinitePlace S harch w] using hw
  have hfinite := Filter.eventually_cofinite.mp hg
  refine ⟨hfinite.toFinset, ?_⟩
  intro w hw
  simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hw

theorem strongApproximation_quaternion_of_volume
    (hnoncompact : ∃ w : LocalAdeles.Place F, w ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints (MatrixGroup.quaternionNormOneMatrixGroup a b) w))
    (hvolume : ∀ T : Finset (ApproximationTopology.AwayPlace S), CompactQuotientProjection.QuotientHasInvariantProbability
      (Ambient.arithmeticAmbientSubgroup (MatrixGroup.quaternionNormOneMatrixGroup a b) S T)) :
    DenseRange (LocalAdeles.diagonalAway (MatrixGroup.quaternionNormOneMatrixGroup a b) S) := by
  obtain ⟨B, hB⟩ := quaternion_exists_exceptional_places a b ha hb S harch
  exact ExceptionalApproximation.strongApproximation_of_volume_and_local_generation (MatrixGroup.quaternionNormOneMatrixGroup a b)
    (GeometricConnected.quaternionNormOneMatrixGroup_connected a b ha hb)
    (GeometricStructure.quaternionNormOneMatrixGroup_absolutelyAlmostSimple a b ha hb)
    (GeometricStructure.quaternionNormOneMatrixGroup_semisimple a b ha hb) S harch hnoncompact hvolume B
    (quaternion_selected_weakApproximation a b ha hb S harch B) hB

end

end OAI.NumberTheory.Quaternion.Arithmetic.StrongApproximationReduction
