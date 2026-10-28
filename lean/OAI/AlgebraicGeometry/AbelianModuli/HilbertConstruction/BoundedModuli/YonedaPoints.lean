import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.IsomorphismFunctor

/-! # Yoneda Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.YonedaPoints

noncomputable section

/-! Evaluation of the Yoneda classifying map specializes the underlying complete isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem boundedFamilyLevelIso_yoneda_point
    {S : Scheme.{u}} {g N n : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) {T M : Over S} (e : IsomorphismFunctor.BoundedFamilyLevelIso A B j P M) (c : T ⟶ M) :
    (((yonedaEquiv (F := IsomorphismFunctor.boundedFamilyLevelIsoFunctor A B j P)).symm e).app (.op T) c).val =
      Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint A B c e.val := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.YonedaPoints
