import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.UniversalCompatibility
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.FamilyDescent

/-! # Universal Family -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.UniversalFamily.GradedHilbert

noncomputable section

/-! The constructed global bounded Hilbert scheme carries an actual
flat proper finitely presented universal closed family in relative projective space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] (n N : ℕ)
variable (S : Scheme.{u}) [IsLocallyNoetherian S] (q : ℕ → ℕ)

def boundedHilbertUniversalFamily :
    Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q) :=
  Hilbert.FamilyDescent.descendedFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
    (fun a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N => NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q)
    (fun a => ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q) (Data.GradedHilbert.boundedHilbertCharts_cover n N S q)
    (UniversalCompatibility.GradedHilbert.boundedHilbertChartUniversalFamily S q) (UniversalCompatibility.GradedHilbert.boundedHilbertChartUniversalFamily_overlap S q)

theorem boundedHilbertUniversalFamily_restriction (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q)
      (boundedHilbertUniversalFamily (ι := ι) n N S q) = UniversalCompatibility.GradedHilbert.boundedHilbertChartUniversalFamily S q a :=
  Hilbert.FamilyDescent.descendedFamily_restriction (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
    (fun a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N => NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q)
    (fun a => ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q) (Data.GradedHilbert.boundedHilbertCharts_cover n N S q)
    (UniversalCompatibility.GradedHilbert.boundedHilbertChartUniversalFamily S q) (UniversalCompatibility.GradedHilbert.boundedHilbertChartUniversalFamily_overlap S q) a

def boundedHilbertUniversalTransformation : yoneda.obj (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q) ⟶
    Hilbert.Functor.familyFunctor (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) where
  app T := ↾fun x => Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x (boundedHilbertUniversalFamily n N S q)
  naturality T U f := by
    ext x
    exact Hilbert.Functor.pullbackFamily_comp (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) f.unop x _

theorem boundedHilbertUniversalTransformation_chart (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N)
    {T : Over S} (x : T ⟶ NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q) :
    (boundedHilbertUniversalTransformation (ι := ι) n N S q).app (.op T)
        (x ≫ ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q) =
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x (UniversalCompatibility.GradedHilbert.boundedHilbertChartUniversalFamily S q a) := by
  change Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (x ≫ ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q) _ = _
  rw [Hilbert.Functor.pullbackFamily_comp, boundedHilbertUniversalFamily_restriction]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.UniversalFamily.GradedHilbert
