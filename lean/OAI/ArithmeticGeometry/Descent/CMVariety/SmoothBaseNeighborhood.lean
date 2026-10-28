import OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedFamily
import OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedSectionCharts
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth

/-! # Smooth Base Neighborhood -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.SmoothBaseNeighborhood.Abelian.RelativeCharts

noncomputable section

/-!
Scheme smoothness constructs a standard-smooth affine base presentation
around any actual complex point. The localized character represents the
original point exactly.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth
open scoped Classical

theorem exists_smooth_affine_base_neighborhood
    (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth S.hom] (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    ∃ (R : CommAlgCat ℂ) (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S),
      IsOpenImmersion b.left ∧ ∃ (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (_P : LocalizedSectionCharts.Abelian.RelativeCharts.ComplexPresentation R),
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap R b y = s := by
  obtain ⟨U, hU, y, hy⟩ := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift S s
  let A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra S U
  let b := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap S U hU
  let : Algebra.Smooth ℂ A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth S U hU
  obtain ⟨a, ha, n, m, ⟨P⟩⟩ := SmoothRelativeNeighborhoods.Abelian.RelativeCharts.exists_relative_submersive_neighborhood (R := ℂ) y
  let R := CommAlgCat.of ℂ (Localization.Away a)
  let b' : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S := LocalizedFamily.Abelian.RelativeCharts.affineAwayMap a ≫ b
  have hb' : IsOpenImmersion b'.left := by
    change IsOpenImmersion ((LocalizedFamily.Abelian.RelativeCharts.affineAwayMap a).left ≫ b.left)
    infer_instance
  refine ⟨R, b', hb', AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint y a ha,
    { VariableIndex := Fin n, RelationIndex := Fin m, presentation := P }, ?_⟩
  exact (LocalizedFamily.Abelian.RelativeCharts.affineAwayMap_point b y a ha).trans hy

end

end OAI.ArithmeticGeometry.Descent.CMVariety.SmoothBaseNeighborhood.Abelian.RelativeCharts
