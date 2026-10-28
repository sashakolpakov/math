import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.GlobalSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison

/-! # Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Total

noncomputable section

/-! Relative extension on the total complex, natural for every actual
map of coefficient complexes, independently of their cohomological degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionNaturality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {X : TopCat.{u}} (U : Opens X)
  {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]

def localFunctor : ((Opens X)ᵒᵖ ⥤ D) ⥤ CochainComplex D ℕ :=
  ExtensionNaturality.sourceFunctor U V

def comparison : localFunctor U V (D := D) ⟶ OrderedCech.Functor.Projection.functor (Intersections.cover U V) :=
  ExtensionNaturality.transformation U V

instance source_additive : (localFunctor U V (D := D)).Additive := by
  change (((Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens X)ᵒᵖ D).obj (Intersections.intersect U).op) ⋙
    AugmentedOrdered.CechFunctor.functor V).Additive
  infer_instance

def source (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) :
    HomologicalComplex₂ D (.up ℕ) (.up ℕ) :=
  ((localFunctor U V).mapHomologicalComplex (.up ℕ)).obj K

def target (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) :
    HomologicalComplex₂ D (.up ℕ) (.up ℕ) :=
  ((OrderedCech.Functor.Projection.functor (Intersections.cover U V)).mapHomologicalComplex (.up ℕ)).obj K

def bicomplexMap (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) : source U V K ⟶ target U V K :=
  ((comparison U V).mapHomologicalComplex (.up ℕ)).app K

variable [HasCoproducts.{0} D]

def map (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) :
    (source U V K).total (.up ℕ) ⟶ (target U V K).total (.up ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap U V K) (.up ℕ)

def sourceMap {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ} (a : K ⟶ L) :
    (source U V K).total (.up ℕ) ⟶ (source U V L).total (.up ℕ) :=
  HomologicalComplex₂.total.map
    (((localFunctor U V).mapHomologicalComplex (.up ℕ)).map a) (.up ℕ)

def targetMap {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ} (a : K ⟶ L) :
    (target U V K).total (.up ℕ) ⟶ (target U V L).total (.up ℕ) :=
  HomologicalComplex₂.total.map
    (((OrderedCech.Functor.Projection.functor (Intersections.cover U V)).mapHomologicalComplex (.up ℕ)).map a) (.up ℕ)

theorem naturality {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ} (a : K ⟶ L) :
    sourceMap U V a ≫ Total.map U V L = Total.map U V K ≫ targetMap U V a := by
  let T := HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map (((comparison U V).mapHomologicalComplex (.up ℕ)).naturality a)).trans
      (T.map_comp _ _))

variable [CategoryWithHomology D]

theorem homology_naturality {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ} (a : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (sourceMap U V a) n ≫
        HomologicalComplex.homologyMap (Total.map U V L) n =
      HomologicalComplex.homologyMap (Total.map U V K) n ≫
        HomologicalComplex.homologyMap (targetMap U V a) n := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun f => HomologicalComplex.homologyMap f n) (Total.naturality U V a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Total
