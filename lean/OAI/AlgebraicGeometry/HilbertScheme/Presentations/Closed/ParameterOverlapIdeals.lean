import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.EqualityByParameterTests
import Mathlib.CategoryTheory.Subfunctor.Basic

/-! # Parameter Overlap Ideals -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ParameterOverlapIdeals

noncomputable section

/-! Closed parameter loci with the same geometric test condition
have identical defining ideals on every overlap. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {B U V W ZU ZV : Over S}

theorem closedParameter_overlap_ideals (F : Subfunctor (yoneda.obj B))
    (b : U ⟶ B) (c : V ⟶ B) (i : ZU ⟶ U) (j : ZV ⟶ V)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (hi : ∀ (T : Over S) (x : T ⟶ U), x ≫ b ∈ F.obj (.op T) ↔ ∃! y : T ⟶ ZU, y ≫ i = x)
    (hj : ∀ (T : Over S) (x : T ⟶ V), x ≫ c ∈ F.obj (.op T) ↔ ∃! y : T ⟶ ZV, y ≫ j = x)
    (p : W ⟶ U) (q : W ⟶ V) (hpq : p ≫ b = q ≫ c) :
    i.left.ker.comap p.left = j.left.ker.comap q.left := by
  apply Ideal.EqualityByParameterTests.ideal_eq_of_over_tests W
  intro T x
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  change i.left.ker.comap (x ≫ p).left = ⊥ ↔ j.left.ker.comap (x ≫ q).left = ⊥
  have he : (x ≫ p) ≫ b = (x ≫ q) ≫ c :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => x ≫ f) hpq).trans (Category.assoc _ _ _).symm)
  have hm : (x ≫ p) ≫ b ∈ F.obj (.op T) ↔ (x ≫ q) ≫ c ∈ F.obj (.op T) := by rw [he]
  exact (FactorizationCriterion.over_closed_factorization_iff_comap_bot i (x ≫ p)).symm.trans
    ((hi T (x ≫ p)).symm.trans
      (hm.trans ((hj T (x ≫ q)).trans (FactorizationCriterion.over_closed_factorization_iff_comap_bot j (x ≫ q)))))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ParameterOverlapIdeals
