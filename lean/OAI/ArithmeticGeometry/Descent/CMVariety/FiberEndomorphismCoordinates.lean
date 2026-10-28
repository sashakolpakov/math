import OAI.ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts

/-! # Fiber Endomorphism Coordinates -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FiberEndomorphismCoordinates.Abelian.RelativeCharts

noncomputable section

/-!
The analytic total-space endomorphism coordinates agree with conjugation
of the actual base-change fiber endomorphism by the sliced fiber chart.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical ContDiff _root_.CategoryTheory.MonObj

variable {R A E F : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}
  {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A} {σ : A →ₐ[ℂ] R}

theorem familyEndomorphismCoordinates_eq_fiber_chart
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (k : G.scheme ⟶ G.scheme)
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G) [IsOpenImmersion i.left]
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x σ)
    (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (q : F)
    (c : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme) E)
    (hs : c.source = (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s)) ⁻¹'
      (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).source)
    (hf : ∀ z ∈ c.source, c z =
      (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) z)).2)
    (hinv : ∀ v ∈ c.target,
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) (c.symm v) =
        (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).symm (q, v))
    (v : E) (hv : v ∈ c.target)
    (himage : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyEndomorphismCharts.Abelian.FamilyPoints.familyEndomorphism S G k)
        ((AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).symm (q, v)) ∈
          (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).source) :
    (FamilyEndomorphismCharts.Abelian.RelativeCharts.familyEndomorphismCoordinates G k i N (q, v)).2 =
      c (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k s) (c.symm v)) := by
  let e := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total
  let inc : (G.pullback s.left).scheme ⟶ AbelianFamilyPoints.FamilyPoints.total S G :=
    AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s
  have hsquare : FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k s ≫ inc =
      inc ≫ FamilyEndomorphismCharts.Abelian.FamilyPoints.familyEndomorphism S G k := FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism_inclusion S G k s
  have he : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s)
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k s) (c.symm v)) =
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyEndomorphismCharts.Abelian.FamilyPoints.familyEndomorphism S G k) (e.symm (q, v)) := by
    change ((c.symm v) ≫ FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k s) ≫ inc =
      (e.symm (q, v)) ≫ FamilyEndomorphismCharts.Abelian.FamilyPoints.familyEndomorphism S G k
    rw [Category.assoc, hsquare, ← Category.assoc]
    exact congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyEndomorphismCharts.Abelian.FamilyPoints.familyEndomorphism S G k)) (hinv v hv)
  have hsource : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k s) (c.symm v) ∈ c.source := by
    rw [hs]
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s)
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k s) (c.symm v)) ∈ e.source
    rw [he]
    exact himage
  change (e (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyEndomorphismCharts.Abelian.FamilyPoints.familyEndomorphism S G k) (e.symm (q, v)))).2 = _
  exact (congrArg (fun z => (e z).2) he).symm.trans (hf _ hsource).symm

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FiberEndomorphismCoordinates.Abelian.RelativeCharts
