import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.OverlapDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackIso

/-! # Concrete Overlap Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection

noncomputable section

/-! One finite coefficient extension makes all actual scheme overlap comparisons isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : IntersectionModel.FiniteIntersectionModel X)

theorem IntersectionModel.FiniteIntersectionModel.exists_common_overlap_pullback_isIso
    (E : Subalgebra M.coefficients R) (hE : E.FG) :
    ∃ D : Subalgebra M.coefficients R, E ≤ D ∧ D.FG ∧
      ∀ j, IsIso ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D)))).map (M.spanComparison j)) := by
  obtain ⟨D, hED, hD, hd⟩ := M.exists_common_overlap_tensor_bijective E hE
  exact ⟨D, hED, hD, fun j => Affine.PullbackIso.isIso_affine_pullback_of_tensor_bijective (M.spanComparison j) (hd j)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection
