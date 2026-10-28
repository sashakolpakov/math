import OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalCoefficient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient

/-! # Quotient Total Image -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.QuotientTotalImage.QuotientTotalHodgeImage

/-! Coefficient reduction followed by the original total comparison
carries each integral form-degree Hodge image into the reduced Hodge image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (R : Type) [CommRing R] (I : Ideal R)

theorem projection_natural {K L : CochainComplex (ModuleCat.{0} R) ℕ} (a : K ⟶ L) :
    a ≫ IntegralComparison.Module.IdealQuotient.complexProjection R I L =
    IntegralComparison.Module.IdealQuotient.complexProjection R I K ≫
      ((IntegralComparison.Module.IdealQuotient.functor R I).mapHomologicalComplex (.up ℕ)).map a := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

variable {K L : HomologicalComplex₂ (ModuleCat.{0} R) (.up ℕ) (.up ℕ)}
  (e : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex (IntegralComparison.Module.IdealQuotient.functor R I) K ≅ L)

def map : K.total (.up ℕ) ⟶ L.total (.up ℕ) :=
  IntegralComparison.Module.IdealQuotient.complexProjection R I (K.total (.up ℕ)) ≫
    (NaturalTotalCoefficient.NaturalTotalCoefficientHodge.totalIso (IntegralComparison.Module.IdealQuotient.functor R I) e).hom

def truncatedMap (r : ℤ) : HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) (.up ℕ) ⟶
    HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r) (.up ℕ) :=
  QuotientTotalHodgeImage.map R I (NaturalTotalCoefficient.NaturalTotalCoefficientHodge.truncatedIso (IntegralComparison.Module.IdealQuotient.functor R I) e r)

theorem inclusion (r : ℤ) :
    HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (.up ℕ) ≫ QuotientTotalHodgeImage.map R I e =
    truncatedMap R I e r ≫ HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ) :=
  ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _
    (projection_natural R I (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (.up ℕ)))
    (NaturalTotalCoefficient.NaturalTotalCoefficientHodge.inclusion_square (IntegralComparison.Module.IdealQuotient.functor R I) e r)

theorem homology_inclusion (n : ℕ) (r : ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (.up ℕ)) n ≫
      HomologicalComplex.homologyMap (QuotientTotalHodgeImage.map R I e) n =
    HomologicalComplex.homologyMap (truncatedMap R I e r) n ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ)) n :=
  (HomologicalComplex.homologyMap_comp
    (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (.up ℕ)) (QuotientTotalHodgeImage.map R I e) n).symm.trans
      ((congrArg (fun a => HomologicalComplex.homologyMap a n) (inclusion R I e r)).trans
        (HomologicalComplex.homologyMap_comp (truncatedMap R I e r)
          (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ)) n))

end NumberTheory.PadicHodge.GeometricComparison.QuotientTotalImage.QuotientTotalHodgeImage

namespace NumberTheory.PadicHodge.GeometricComparison.QuotientTotalImage.QuotientBicomplexProjection

/-! The original coefficient quotient projection commutes with
the original finite total comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (R : Type) [CommRing R] (I : Ideal R)
  (K : HomologicalComplex₂ (ModuleCat.{0} R) (.up ℕ) (.up ℕ))

def bicomplex : K ⟶ AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex (IntegralComparison.Module.IdealQuotient.functor R I) K where
  f q := IntegralComparison.Module.IdealQuotient.complexProjection R I (K.X q)
  comm' q r _ := (QuotientTotalHodgeImage.projection_natural R I (K.d q r)).symm

theorem total : HomologicalComplex₂.total.map (bicomplex R I K) (.up ℕ) ≫
    AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison (IntegralComparison.Module.IdealQuotient.functor R I) K =
      IntegralComparison.Module.IdealQuotient.complexProjection R I (K.total (.up ℕ)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro q r h
  change K.ιTotal (.up ℕ) q r n h ≫
      ((HomologicalComplex₂.total.map (bicomplex R I K) (.up ℕ)).f n ≫
        AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonComponent (IntegralComparison.Module.IdealQuotient.functor R I) K n) =
    K.ιTotal (.up ℕ) q r n h ≫ (IntegralComparison.Module.IdealQuotient.complexProjection R I (K.total (.up ℕ))).f n
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc,
    AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.ι_totalComparisonComponent]
  exact ((IntegralComparison.Module.IdealQuotient.projection R I).naturality (K.ιTotal (.up ℕ) q r n h)).symm

theorem inverse : IntegralComparison.Module.IdealQuotient.complexProjection R I (K.total (.up ℕ)) ≫
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso (IntegralComparison.Module.IdealQuotient.functor R I) K).inv =
      HomologicalComplex₂.total.map (bicomplex R I K) (.up ℕ) := by
  let e := AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso (IntegralComparison.Module.IdealQuotient.functor R I) K
  exact (congrArg (fun a => a ≫ e.inv) (QuotientBicomplexProjection.total R I K).symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a => HomologicalComplex₂.total.map (bicomplex R I K) (.up ℕ) ≫ a) e.hom_inv_id).trans
        (Category.comp_id _)))

end NumberTheory.PadicHodge.GeometricComparison.QuotientTotalImage.QuotientBicomplexProjection

end

end OAI
