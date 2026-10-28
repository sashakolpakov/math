import OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies

/-! # Intrinsic Morphism Overlap -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicMorphismOverlap

noncomputable section

/-! An actual scheme morphism is holomorphic on its entire overlap with
the supplied analytic affine chart. The domain retains both chart tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical ContDiff

open OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies.Abelian.RelativeCharts

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

theorem native_morphism_coordinates_contDiffOn
    (A : CommAlgCat ℂ) (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ Y) [IsOpenImmersion i.left]
    (c : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) F)
    (hc : ArithmeticGeometry.Descent.CMVariety.RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates c)
    (hinv : ∀ a : A, ContDiffOn ℂ ω (fun z => c.symm z a) c.target)
    (k : Y ⟶ Y) :
    let e := ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart A i c
    let D := e.target ∩ (fun z => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k (e.symm z)) ⁻¹' e.source
    IsOpen D ∧ ContDiffOn ℂ ω (fun z => e (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k (e.symm z))) D := by
  let e := ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart A i c
  let f := fun z => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A (i ≫ k) (c.symm z)
  have hpoint (z : F) : f z = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k (e.symm z) :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp A i k (c.symm z)
  have hD := ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies.Abelian.RelativeCharts.isOpen_schemeImage_affineChart_domain A A (i ≫ k) i c
    c.symm c.target c.open_target hinv
  have h := ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies.Abelian.RelativeCharts.contDiffOn_schemeImage_in_affineChart A A (i ≫ k) i c hc
    c.symm c.target c.open_target hinv
  have hset : c.target ∩ {z | f z ∈ e.source} =
      e.target ∩ (fun z => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k (e.symm z)) ⁻¹' e.source := by
    ext z
    change (z ∈ c.target ∧ f z ∈ e.source) ↔
      (z ∈ c.target ∧ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k (e.symm z) ∈ e.source)
    rw [hpoint]
  refine ⟨hset ▸ hD, ?_⟩
  rw [← hset]
  apply h.congr
  intro z _
  exact congrArg e (hpoint z).symm

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicMorphismOverlap
