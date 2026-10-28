import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantFrameNormalizationValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.ProjectiveCoordinateAction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Polynomials

/-! # Point Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.PointNormalization

noncomputable section

/-! The determinant-unit frame condition yields an actual relative
projective automorphism sending the labeled frame to the standard frame,
as equalities of scheme morphisms over the base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (S : Scheme.{u}) {n : ℕ}

theorem scalarCoordinateProjectivePoint_eq_of_unit_mul
    (v w : Fin (n + 1) → Γ(S, ⊤)) (u : Γ(S, ⊤)ˣ)
    (he : ∀ i, v i = (u : Γ(S, ⊤)) * w i)
    (hv : ∀ x : S, ∃ i, x ∈ S.basicOpen (v i))
    (hw : ∀ x : S, ∃ i, x ∈ S.basicOpen (w i)) :
    Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv = Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint w hw := by
  have h : v = fun i => (u : Γ(S, ⊤)) * w i := funext he
  subst v
  exact Scalar.CoordinateProjectivePoints.scalarCoordinateProjectivePoint_unit_mul S n w u hw hv

theorem projectiveFrame_exists_normalizing_automorphism
    (b : Fin (n + 1) → Fin (n + 1) → Γ(S, ⊤)) (v : Fin (n + 1) → Γ(S, ⊤))
    (h : IsUnit (Polynomials.vectorFrameDiscriminant b v))
    (hb : ∀ i, ∀ x : S, ∃ k, x ∈ S.basicOpen (b i k))
    (hv : ∀ x : S, ∃ k, x ∈ S.basicOpen (v k)) :
    ∃ α : Projective.ProjectivePresentations.projectiveSpaceOver S n ≅ Projective.ProjectivePresentations.projectiveSpaceOver S n,
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv ≫ α.hom = Scalar.CoordinateProjectivePoints.allOneProjectivePoint S n ∧
      ∀ i, Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (b i) (hb i) ≫ α.hom = Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint S n i := by
  let e := Pi.basisFun Γ(S, ⊤) (Fin (n + 1))
  let T := DeterminantFrameLinearMap.determinantFrameLinearEquiv e b v h
  obtain ⟨⟨u, hu⟩, ha⟩ := DeterminantFrameNormalizationValues.determinantFrameLinearMap_normalizes e b v h
  have huv : ∀ k, T v k = (u : Γ(S, ⊤)) := fun k => congrFun hu k
  have hTv : ∀ x : S, ∃ k, x ∈ S.basicOpen (T v k) := by
    intro x
    refine ⟨0, ?_⟩
    rw [huv]
    exact (S.basicOpen_of_isUnit u.isUnit).symm ▸ trivial
  refine ⟨Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).symm, ?_, ?_⟩
  · rw [Scalar.ProjectiveCoordinateAction.scalarCoordinateProjectivePoint_linear_action S v T hv hTv]
    apply scalarCoordinateProjectivePoint_eq_of_unit_mul S (T v) (fun _ => 1) u
      (fun k => (huv k).trans (mul_one _).symm) hTv
      (Scalar.CoordinateProjectivePoints.allOneProjectiveCoordinates_cover S n)
  · intro i
    obtain ⟨a, hi⟩ := ha i
    have hi' (k : Fin (n + 1)) : T (b i) k = if i = k then (a : Γ(S, ⊤)) else 0 := by
      by_cases hik : i = k <;> simpa [T, DeterminantFrameLinearMap.determinantFrameLinearEquiv, hik] using hi k
    have hTi : ∀ x : S, ∃ k, x ∈ S.basicOpen (T (b i) k) := by
      intro x
      refine ⟨i, ?_⟩
      rw [show T (b i) i = (a : Γ(S, ⊤)) by simpa using hi' i]
      exact (S.basicOpen_of_isUnit a.isUnit).symm ▸ trivial
    rw [Scalar.ProjectiveCoordinateAction.scalarCoordinateProjectivePoint_linear_action S (b i) T (hb i) hTi]
    apply scalarCoordinateProjectivePoint_eq_of_unit_mul S (T (b i))
      (Scalar.CoordinateProjectivePoints.standardBasisProjectiveCoordinates S n i) a _ hTi
      (Scalar.CoordinateProjectivePoints.standardBasisProjectiveCoordinates_cover S n i)
    intro k
    change T (b i) k = (a : Γ(S, ⊤)) * (if i = k then 1 else 0)
    rw [show T (b i) k = if i = k then (a : Γ(S, ⊤)) else 0 from hi' k]
    split_ifs <;> simp only [mul_one, mul_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.PointNormalization
