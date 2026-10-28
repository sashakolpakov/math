import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.De
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.DerivedSheafBetti

/-! # Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Map

noncomputable section

/-!
# The constructed algebraic de Rham–Betti map

Actual algebraic forms are realized on the analytification, the proved
analytic de Rham resolution gives constant-sheaf cohomology, and the proved
singular-cochain comparison gives Betti cohomology. The algebraic–analytic
isomorphism theorem and the final naturality theorem remain separate work.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

/-- Analytic constant-sheaf cohomology is actual singular cohomology. -/
def analyticConstantBettiIso (n : ℕ) : Analytic.De.analyticConstantCohomology X n ≅ Sheaves.betti X n := by
  have : StronglyLocallyContractibleSpace (Betti.Scheme.schemePointSpace X) :=
    AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace
      (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  have : MetrizableSpace (Betti.Scheme.schemePointSpace X) :=
    inferInstanceAs (MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
  let e := Derived.DerivedSheafBetti.singularConstantCohomologyIso (Betti.Scheme.schemePointSpace X) n
  exact e.symm

/-- The comparison map is assembled from actual sheaf and cochain constructions. -/
def algebraicDeRhamBettiMap (n : ℕ) : Sheaves.algebraicDeRham X n ⟶ Sheaves.betti X n :=
  Analytic.De.algebraicToAnalyticCohomologyMap X n ≫ (analyticConstantBettiIso X n).hom

theorem algebraicDeRhamBettiMap_factorization (n : ℕ) :
    algebraicDeRhamBettiMap X n ≫ (analyticConstantBettiIso X n).inv =
      Analytic.De.algebraicToAnalyticCohomologyMap X n := by
  simp only [algebraicDeRhamBettiMap, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Map
