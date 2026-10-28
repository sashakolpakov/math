import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.TotalHomotopy

/-! # Cech Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechHomotopy

noncomputable section

/-! Homotopies of presheaf complexes induce the same map on the
genuine augmented ordered Čech total cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w
variable {R : Type u} [CommRing R] {C : Type v} [Preorder C] [HasFiniteProducts C]
  {ι : Type v} [LinearOrder ι] (U : ι → C)
  [HasProducts.{v} (ModuleCat.{w} R)]
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ} {f g : K ⟶ L}

local instance totalExists (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ) :
    (CechFunctor.bicomplex U P).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

theorem homology (h : Homotopy f g) (i : ℕ) :
    HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map (((CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map f) (.up ℕ)) i =
      HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map (((CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map g) (.up ℕ)) i :=
  AlgebraicGeometry.Crystalline.Cohomology.Module.TotalHomotopy.ModuleTotalHomotopy.homology ((CechFunctor.functor U).mapHomotopy h) i

theorem homology_comp {M : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ}
    (a : K ⟶ L) (b : L ⟶ M) (i : ℕ) :
    HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map (((CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map (a ≫ b)) (.up ℕ)) i =
      HomologicalComplex.homologyMap
          (HomologicalComplex₂.total.map (((CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map a) (.up ℕ)) i ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex₂.total.map (((CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map b) (.up ℕ)) i := by
  rw [Functor.map_comp, HomologicalComplex₂.total.map_comp, HomologicalComplex.homologyMap_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechHomotopy
