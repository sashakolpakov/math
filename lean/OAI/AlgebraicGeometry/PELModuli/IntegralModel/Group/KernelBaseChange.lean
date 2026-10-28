import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.PointsBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Kernel Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.KernelBaseChange.GroupPoints

noncomputable section

/-! Exact full-kernel functors commute with base change. The proof uses
the actual group-valued pullback adjunction on arbitrary test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S S' : Scheme} {A B R : Over S} [GrpObj A] [GrpObj B] [GrpObj R]
  (f : S' ⟶ S)

theorem baseChangePoints_map (p : A ⟶ B) (T : Over S') (x : T ⟶ (Over.pullback f).obj A) :
    PointsBaseChange.GroupPoints.baseChangePointsMulEquiv B f T (x ≫ (Over.pullback f).map p) =
      PointsBaseChange.GroupPoints.baseChangePointsMulEquiv A f T x ≫ p := by
  apply Over.OverMorphism.ext
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => x.left ≫ a) (AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst p f)).trans
      (Category.assoc _ _ _).symm)

/-- An actual kernel inclusion remains the full kernel after arbitrary
base change, with no restriction on the test schemes. -/
theorem kernel_baseChange (p : A ⟶ B) [IsMonHom p] (i : R ⟶ A) [IsMonHom i]
    (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ p = 1 ↔ ∃ r : T ⟶ R, r ≫ i = x)
    (T : Over S') (x : T ⟶ (Over.pullback f).obj A) :
    x ≫ (Over.pullback f).map p = 1 ↔
      ∃ r : T ⟶ (Over.pullback f).obj R, r ≫ (Over.pullback f).map i = x := by
  let eA := PointsBaseChange.GroupPoints.baseChangePointsMulEquiv A f T
  let eB := PointsBaseChange.GroupPoints.baseChangePointsMulEquiv B f T
  let eR := PointsBaseChange.GroupPoints.baseChangePointsMulEquiv R f T
  have hz : x ≫ (Over.pullback f).map p = 1 ↔ eA x ≫ p = 1 := by
    constructor
    · intro h
      exact (baseChangePoints_map f p T x).symm.trans
        ((congrArg eB h).trans eB.map_one)
    · intro h
      apply eB.injective
      exact (baseChangePoints_map f p T x).trans (h.trans eB.map_one.symm)
  rw [hz, hk]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨eR.symm r, ?_⟩
    apply eA.injective
    exact (baseChangePoints_map f i T (eR.symm r)).trans
      ((congrArg (fun r => r ≫ i) (eR.apply_symm_apply r)).trans hr)
  · rintro ⟨r, hr⟩
    exact ⟨eR r, (baseChangePoints_map f i T r).symm.trans (congrArg eA hr)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.KernelBaseChange.GroupPoints
