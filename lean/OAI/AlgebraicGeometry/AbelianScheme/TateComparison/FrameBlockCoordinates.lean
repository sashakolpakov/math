import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitBlocks
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Lattices

/-! # Frame Block Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! A frame respecting the actual integral PEL action respects its
completed split action. Consequently each actual integral Tate block
has only its own coordinate in that frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.IsGoodCompletelySplitPrime)
  {S : Scheme} (T : Over S)
  (F : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S)
  (e : Rational.SplitTateFrame s F.abelian.scheme T q)
  (he : Rational.IsSplitActionFrame F T q D.localCharacter e)

def Data.SphericalPELAlbaneseData.integralFrameCoordinate (v : Fin s × Bool) (i : Fin 3) :
    Add.schemeTateModule F.abelian.scheme T q →ₗ[ℤ_[q]] ℚ_[q] :=
  ((LinearMap.proj i).comp ((LinearMap.proj v).comp (e.restrictScalars ℤ_[q]).toLinearMap)).comp
    (TensorProduct.mk ℤ_[q] ℚ_[q] (Add.schemeTateModule F.abelian.scheme T q) 1)

theorem Data.SphericalPELAlbaneseData.integralFrameCoordinate_apply (v : Fin s × Bool) (i : Fin 3)
    (x : Add.schemeTateModule F.abelian.scheme T q) :
    D.integralFrameCoordinate T F e v i x = e (1 ⊗ₜ[ℤ_[q]] x) v i := rfl

include he in
theorem Data.SphericalPELAlbaneseData.integralFrameCoordinate_action (r : NumberField.RingOfIntegers E)
    (x : Add.schemeTateModule F.abelian.scheme T q) (v : Fin s × Bool) (i : Fin 3) :
    D.integralFrameCoordinate T F e v i (TateAction.tateIntegralAction T q F r x) =
      D.localCharacter v r • D.integralFrameCoordinate T F e v i x := by
  have hx := he r (1 ⊗ₜ[ℤ_[q]] x) v i
  rw [Lattices.rationalTateMap_integral] at hx
  change e (1 ⊗ₜ[ℤ_[q]] (TateAction.tateEndMap F.abelian.scheme T q (F.action r)) x) v i = _
  rw [TateAction.tateEndMap_eq_schemeTateMap]
  exact hx

include he in
theorem Data.SphericalPELAlbaneseData.integralFrameCoordinate_completed (a : ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E)
    (x : Add.schemeTateModule F.abelian.scheme T q) (v : Fin s × Bool) (i : Fin 3) :
    D.integralFrameCoordinate T F e v i (TateAction.tateCompletedAction T q F a x) =
      D.localCompletionMapZq a v • D.integralFrameCoordinate T F e v i x := by
  induction a using TensorProduct.inductionOn with
  | tmul z r =>
    rw [TateAction.tateCompletedAction_tmul]
    change D.integralFrameCoordinate T F e v i (z • TateAction.tateIntegralAction T q F r x) =
      (z * D.localCharacter v r) • D.integralFrameCoordinate T F e v i x
    rw [map_smul, D.integralFrameCoordinate_action T F e he, mul_smul]
  | add a b ha hb =>
    rw [map_add, LinearMap.add_apply, map_add, ha, hb, map_add]
    exact (add_smul _ _ _).symm

include he in
theorem Data.SphericalPELAlbaneseData.integralFrameCoordinate_split (a : Fin s × Bool → ℤ_[q])
    (x : Add.schemeTateModule F.abelian.scheme T q) (v : Fin s × Bool) (i : Fin 3) :
    D.integralFrameCoordinate T F e v i (D.splitTateAction h T F a x) =
      a v • D.integralFrameCoordinate T F e v i x := by
  have hx := D.integralFrameCoordinate_completed T F e he
    ((D.localCompletionEquivZq h).symm a) x v i
  change D.integralFrameCoordinate T F e v i (D.splitTateAction h T F a x) =
    D.localCompletionEquivZq h ((D.localCompletionEquivZq h).symm a) v •
      D.integralFrameCoordinate T F e v i x at hx
  rwa [AlgEquiv.apply_symm_apply] at hx

include he in
theorem Data.SphericalPELAlbaneseData.integralFrameCoordinate_off_block {w v : Fin s × Bool} (hwv : w ≠ v)
    (x : D.integralTateBlock h T F w) (i : Fin 3) :
    e (1 ⊗ₜ[ℤ_[q]] x.val) v i = 0 := by
  classical
  have hx := D.integralFrameCoordinate_split h T F e he (Pi.single w 1) x.val v i
  rw [← ProductActionDecomposition.ProductAction.projector_eq_single,
    ProductActionDecomposition.ProductAction.projector_on_block (D.splitTateAction h T F) w x,
    Pi.single_eq_of_ne hwv.symm, zero_smul, Data.SphericalPELAlbaneseData.integralFrameCoordinate_apply] at hx
  exact hx

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
