import OAI.AlgebraicGeometry.ComplexMultiplication.ProjectivePresentationComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.AbelianGroups
import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety

/-! # Bundled Abelian Bridge -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge

noncomputable section

/-! # The original geometric domain in the actual older abelian-variety bundle

The projective presentation is transported along the proved projective scheme
isomorphism. The carrier, complex-field structure map and algebraic group law
are the unchanged original ones. No cohomological assumption is supplied.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

private theorem complexProjectiveSpaceIso_inv_over (n : ℕ) :
    (ProjectivePresentationComparison.ProjectiveCharts.complexProjectiveSpaceIso n).inv ≫
      Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n =
        Foundations.ProjectiveSpaceIs.ProjectiveSpace.toBase (Fin (n + 1)) (Spec (.of ℂ)) := by
  rw [← ProjectivePresentationComparison.ProjectiveCharts.complexProjectiveSpaceIso_over n, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- The original scheme with a proved actual complex-coefficient projective presentation. -/
def originalIntegralProjectiveVariety : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := by
  let P := Classical.choice (inferInstance : Foundations.ProjectiveSpaceIs.IsProjective X.hom).nonempty_presentation
  letI : IsClosedImmersion P.immersion := P.isClosedImmersion
  let i := P.immersion ≫ (ProjectivePresentationComparison.ProjectiveCharts.complexProjectiveSpaceIso P.ambientDimension).inv
  have hi : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  have hover : i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase P.ambientDimension = X.hom := by
    dsimp only [i]
    rw [Category.assoc, complexProjectiveSpaceIso_inv_over]
    exact P.immersion_toBase
  exact Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.ofClosedImmersion X.hom
    P.ambientDimension i hi hover inferInstance inferInstance

/-- The comparison changes only the presentation, retaining the exact original object over ℂ. -/
@[simp]
theorem originalIntegralProjectiveVariety_toOver :
    (originalIntegralProjectiveVariety X).toOver = X := rfl

variable [GrpObj X]

/-- The actual older abelian-variety bundle, with the unchanged original algebraic group law. -/
def originalAbelianVariety : CMAbelianVariety.CM.AbelianVariety where
  variety := originalIntegralProjectiveVariety X
  group := by
    change GrpObj X
    infer_instance
  commutative := by
    change IsCommMonObj X
    infer_instance

/-- The actual abelian-variety bundle has precisely the original carrier and structure map. -/
@[simp]
theorem originalAbelianVariety_toOver : (originalAbelianVariety X).toOver = X := rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge
