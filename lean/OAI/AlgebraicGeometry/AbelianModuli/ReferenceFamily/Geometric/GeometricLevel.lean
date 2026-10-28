import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientLevelCover
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points

/-! # Geometric Level -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.GeometricLevel

noncomputable section

/-! Actual full ordered levels over every algebraically closed field
of characteristic zero, obtained from the constructed coefficient model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {g L N : ℕ} {δ : Fin g → ℕ}

omit [CharZero k] in
theorem geometricFullLevel_of_cover (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (p : Spec (.of k) ⟶ Spec (.of ℚ)) [NeZero L]
    [Surjective (Frame.Locus.LevelCover.fullFrameScheme A p (N := L)).hom] : Nonempty (A.FullLevel L) := by
  let F := Frame.Locus.LevelCover.fullFrameScheme A p (N := L)
  let j : F ⟶ ConstantSectionsOn.ConstantSections.baseTest (Spec (.of k)) := Over.homMk F.hom (Category.comp_id _)
  let : Surjective j.left := inferInstanceAs (Surjective (Frame.Locus.LevelCover.fullFrameScheme A p (N := L)).hom)
  let : Etale F.hom := (Frame.Locus.LevelCover.fullFrameScheme_finite_etale A p (N := L)).2
  let : LocallyOfFiniteType j.left := inferInstanceAs (LocallyOfFiniteType F.hom)
  obtain ⟨q, _⟩ := AbelianScheme.IsogenyQuotient.Geometric.Points.Construction.surjective_on_geometric_points j k
    (𝟙 (Spec (.of k))) (𝟙 (ConstantSectionsOn.ConstantSections.baseTest (Spec (.of k))))
  exact ⟨@HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.transport g L (Spec (.of k))
    (A.pullback (𝟙 (Spec (.of k)))) A
    (Frame.Factorization.LevelCover.fullFramePointsEquiv A p (ConstantSectionsOn.ConstantSections.baseTest (Spec (.of k))) q)
    A.pullbackIdIso A.pullbackIdIso_preservesGroup⟩

theorem geometricPolarized_exists_fullLevel
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) (L : ℕ) [NeZero L] :
    Nonempty (A.abelian.FullLevel L) := by
  obtain ⟨D⟩ := AbelianModel.geometricPolarized_has_abelian_model A
  let p := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ k D.data.toModel.coefficients ≫
    CoefficientLevelCover.rationalCoefficientBaseMap D.data.toModel.coefficients
  let : Surjective (Frame.Locus.LevelCover.fullFrameScheme A.abelian p (N := L)).hom :=
    CoefficientLevelCover.geometric_fullFrame_surjective_of_model A.abelian D
  exact geometricFullLevel_of_cover A.abelian p

def geometricPolarizedFullLevel
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) (L : ℕ) [NeZero L] :
    A.abelian.FullLevel L := Classical.choice (geometricPolarized_exists_fullLevel A L)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.GeometricLevel
