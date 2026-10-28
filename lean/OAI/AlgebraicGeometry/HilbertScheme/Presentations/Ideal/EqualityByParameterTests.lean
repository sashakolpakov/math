import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.FactorizationCriterion

/-! # Equality By Parameter Tests -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.EqualityByParameterTests

noncomputable section

/-! Actual ideal sheaves are determined by their closed-subscheme
factorization conditions on all parameter tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (B : Over S)

theorem ideal_eq_of_over_tests (I J : B.left.IdealSheafData)
    (h : ∀ (T : Over S) (x : T ⟶ B), I.comap x.left = ⊥ ↔ J.comap x.left = ⊥) : I = J := by
  have hle (I J : B.left.IdealSheafData)
      (h : ∀ (T : Over S) (x : T ⟶ B), I.comap x.left = ⊥ → J.comap x.left = ⊥) : J ≤ I := by
    let T : Over S := Over.mk (I.subschemeι ≫ B.hom)
    let x : T ⟶ B := Over.homMk I.subschemeι rfl
    have hi : I.comap x.left = ⊥ := by
      change I.comap I.subschemeι = ⊥
      exact (congrArg (fun K : B.left.IdealSheafData => K.comap I.subschemeι)
        I.ker_subschemeι).symm.trans (Closed.ImmersionOverlapLifts.kernel_comap_self I.subschemeι)
    have hj := h T x hi
    have hm : J ≤ (⊥ : I.subscheme.IdealSheafData).map I.subschemeι :=
      Scheme.IdealSheafData.le_map_iff_comap_le.mpr hj.le
    simpa only [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι] using hm
  exact le_antisymm (hle J I (fun T x => (h T x).mpr)) (hle I J (fun T x => (h T x).mp))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.EqualityByParameterTests
