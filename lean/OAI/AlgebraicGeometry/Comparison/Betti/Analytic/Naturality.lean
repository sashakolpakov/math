import OAI.AlgebraicGeometry.Comparison.Betti.Derived.SheafNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Map

/-! # Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytic.Naturality

noncomputable section

/-! The actual analytic constant-sheaf-to-Betti comparison is natural for scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

def analyticConstantPullback (n : ℕ) : De.analyticConstantCohomology Y n ⟶ De.analyticConstantCohomology X n :=
  Derived.ConstantPullback.constantDerivedPullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) n

variable [IsIntegral X.left] [Smooth X.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  [IsIntegral Y.left] [Smooth Y.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]

theorem analyticConstantBettiIso_naturality (n : ℕ) :
    analyticConstantPullback f n ≫ (Algebraic.Map.analyticConstantBettiIso X n).hom =
      (Algebraic.Map.analyticConstantBettiIso Y n).hom ≫ Algebraic.Sheaves.bettiPullback f n := by
  have : StronglyLocallyContractibleSpace (Betti.Scheme.schemePointSpace X) :=
    AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  have : StronglyLocallyContractibleSpace (Betti.Scheme.schemePointSpace Y) :=
    AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace (RegularSmoothness.NativeModel Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
  have : MetrizableSpace (Betti.Scheme.schemePointSpace X) := inferInstanceAs (MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
  have : MetrizableSpace (Betti.Scheme.schemePointSpace Y) := inferInstanceAs (MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
  let eX := Derived.DerivedSheafBetti.singularConstantCohomologyIso (Betti.Scheme.schemePointSpace X) n
  let eY := Derived.DerivedSheafBetti.singularConstantCohomologyIso (Betti.Scheme.schemePointSpace Y) n
  have h : Algebraic.Sheaves.bettiPullback f n ≫ eX.hom = eY.hom ≫ analyticConstantPullback f n :=
    Derived.SheafNaturality.singularConstantCohomologyIso_naturality (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) n
  change analyticConstantPullback f n ≫ eX.inv = eY.inv ≫ Algebraic.Sheaves.bettiPullback f n
  apply (Iso.cancel_iso_hom_left eY _ _).mp
  erw [eY.hom_inv_id_assoc, ← Category.assoc, ← h, Category.assoc, eX.hom_inv_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytic.Naturality
