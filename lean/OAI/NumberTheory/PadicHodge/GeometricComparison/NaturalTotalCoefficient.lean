import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalCoefficientComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedFunctorIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor

/-! # Natural Total Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalCoefficient.NaturalTotalCoefficientHodge

noncomputable section

/-! Actual additive coefficient comparison of nonnegative totals
preserves form-degree Hodge inclusions on homology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D]
  (F : C ⥤ D) [F.Additive]
  {K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)}
  {L : HomologicalComplex₂ D (.up ℕ) (.up ℕ)}
  (e : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K ≅ L)

def totalIso : (F.mapHomologicalComplex (.up ℕ)).obj (K.total (.up ℕ)) ≅ L.total (.up ℕ) :=
  (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K).symm ≪≫ HomologicalComplex₂.total.mapIso e (.up ℕ)

variable {K' : HomologicalComplex₂ C (.up ℕ) (.up ℕ)}
  {L' : HomologicalComplex₂ D (.up ℕ) (.up ℕ)}
  (e' : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K' ≅ L') (a : K ⟶ K') (b : L ⟶ L')
  (h : TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap F a ≫ e'.hom = e.hom ≫ b)

include h in
theorem naturality : (F.mapHomologicalComplex (.up ℕ)).map (HomologicalComplex₂.total.map a (.up ℕ)) ≫
    (totalIso F e').hom = (totalIso F e).hom ≫ HomologicalComplex₂.total.map b (.up ℕ) := by
  have h₁ := IntegralComparison.InverseCoordinateHomology.inverse
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K) (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K')
    (HomologicalComplex₂.total.map (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap F a) (.up ℕ))
    ((F.mapHomologicalComplex (.up ℕ)).map (HomologicalComplex₂.total.map a (.up ℕ)))
    (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.natural F a)
  let T := HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ)
  have h₂ := congrArg T.map h
  simp only [Functor.map_comp] at h₂
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

def truncatedIso (r : ℤ) : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) ≅ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r :=
  TruncatedFunctorIso.TruncatedPullback.iso (F.mapHomologicalComplex (.up ℕ)) e r

theorem inclusion_square (r : ℤ) :
    (F.mapHomologicalComplex (.up ℕ)).map
      (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (.up ℕ)) ≫ (totalIso F e).hom =
    (totalIso F (truncatedIso F e r)).hom ≫
      HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ) :=
  naturality F (truncatedIso F e r) e (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r)
    (TruncatedFunctorIso.TruncatedPullback.iso_inclusion (F.mapHomologicalComplex (.up ℕ)) e r).symm

variable [F.PreservesHomology]

def homologyIso (n : ℕ) : F.obj ((K.total (.up ℕ)).homology n) ≅ (L.total (.up ℕ)).homology n :=
  ExactHomology.ExactHomologyComparison.iso F (.up ℕ) _ _ (totalIso F e) n

theorem homology_inclusion (n : ℕ) (r : ℤ) :
    F.map (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (.up ℕ)) n) ≫ (homologyIso F e n).hom =
    (homologyIso F (truncatedIso F e r) n).hom ≫ HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ)) n :=
  ExactHomology.ExactHomologyComparison.naturality F (.up ℕ) (totalIso F (truncatedIso F e r)) (totalIso F e)
    (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (.up ℕ))
    (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ))
    (inclusion_square F e r) n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalCoefficient.NaturalTotalCoefficientHodge
