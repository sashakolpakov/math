import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.BaseChange

/-! # Point Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Base-valued points have a canonical base change, and nonidentity points remain nonidentity under an epimorphic change of base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

def Base.PointChange.baseChangeUnitMap {S S' : Scheme.{u}} (c : S' ⟶ S) :
    (Over.map c).obj (𝟙_ (Over S')) ⟶ 𝟙_ (Over S) :=
  Over.homMk c (by simp)

variable {S S' : Scheme.{u}} {g : ℕ} (B : Abelian.Schemes.AbelianScheme g S) (c : S' ⟶ S)

def Abelian.Schemes.AbelianScheme.basePointPullback (x : 𝟙_ (Over S) ⟶ B.scheme) :
    𝟙_ (Over S') ⟶ (B.pullback c).scheme :=
  (B.baseChangePointsMulEquiv c (𝟙_ (Over S'))).symm (Base.PointChange.baseChangeUnitMap c ≫ x)

theorem Abelian.Schemes.AbelianScheme.basePointPullback_comparison (x : 𝟙_ (Over S) ⟶ B.scheme) :
    B.baseChangePointsEquiv c (𝟙_ (Over S')) (B.basePointPullback c x) =
      Base.PointChange.baseChangeUnitMap c ≫ x :=
  (B.baseChangePointsMulEquiv c (𝟙_ (Over S'))).apply_symm_apply _

theorem Abelian.Schemes.AbelianScheme.basePointPullback_one : B.basePointPullback c (1 : 𝟙_ (Over S) ⟶ B.scheme) = 1 := by
  change (B.baseChangePointsMulEquiv c (𝟙_ (Over S'))).symm (Base.PointChange.baseChangeUnitMap c ≫ 1) = 1
  rw [MonObj.comp_one, map_one]

theorem Abelian.Schemes.AbelianScheme.basePointPullback_injective [Epi c] : Function.Injective (B.basePointPullback c) := by
  have : Epi (Base.PointChange.baseChangeUnitMap c).left := inferInstanceAs (Epi c)
  have : Epi (Base.PointChange.baseChangeUnitMap c) := Over.epi_of_epi_left _
  intro x y h
  apply (cancel_epi (Base.PointChange.baseChangeUnitMap c)).mp
  exact (B.basePointPullback_comparison c x).symm.trans
    ((congrArg (B.baseChangePointsEquiv c (𝟙_ (Over S'))) h).trans
      (B.basePointPullback_comparison c y))

theorem Abelian.Schemes.AbelianScheme.basePointPullback_ne_one [Epi c] (x : 𝟙_ (Over S) ⟶ B.scheme) (hx : x ≠ 1) :
    B.basePointPullback c x ≠ 1 := by
  intro h
  apply hx
  apply B.basePointPullback_injective c
  exact h.trans (B.basePointPullback_one c).symm

theorem Abelian.Schemes.AbelianScheme.basePointPullback_ne_one_of_flat_surjective [Flat c] [Surjective c]
    (x : 𝟙_ (Over S) ⟶ B.scheme) (hx : x ≠ 1) : B.basePointPullback c x ≠ 1 := by
  have : Epi c := Flat.epi_of_flat_of_surjective c
  exact B.basePointPullback_ne_one c x hx

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
