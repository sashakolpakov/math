import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexComposition
import Mathlib.Algebra.Homology.Homotopy

/-! # Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.Homotopy

noncomputable section

/-! Homotopic original sheaf maps induce the same constant-coefficient section comparison on homology. -/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max w z} (Sheaf J (ModuleCat.{w} R))]
  (D : CochainComplex (ModuleCat.{w} R) ℕ)
  {K L : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ}
  (a : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℕ)).obj D ⟶ K)
  (b c : K ⟶ L) (h : Homotopy b c)

include h in
theorem mapped (i : ℕ) :
    HomologicalComplex.homologyMap
      (((Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0).mapHomologicalComplex
        (.up ℕ)).map b) i =
    HomologicalComplex.homologyMap
      (((Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0).mapHomologicalComplex
        (.up ℕ)).map c) i :=
  ((Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0).mapHomotopy h).homologyMap_eq i

include h in
theorem precomposed (i : ℕ) :
    HomologicalComplex.homologyMap
      (ComplexMap.map.{u, v, w, z} R J D K a ≫
        ((Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0).mapHomologicalComplex
          (.up ℕ)).map b) i =
    HomologicalComplex.homologyMap
      (ComplexMap.map.{u, v, w, z} R J D K a ≫
        ((Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0).mapHomologicalComplex
          (.up ℕ)).map c) i := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max w z} R) (.up ℕ) i
  let S : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{max w z} R :=
    Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0
  let T := S.mapHomologicalComplex (.up ℕ)
  let d := ComplexMap.map.{u, v, w, z} R J D K a
  exact (H.map_comp d (T.map b)).trans
    ((congrArg (fun t => H.map d ≫ t) (mapped.{u, v, w, z} R J b c h i)).trans
      (H.map_comp d (T.map c)).symm)

include h in
theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap (ComplexMap.map.{u, v, w, z} R J D L (a ≫ b)) i =
      HomologicalComplex.homologyMap (ComplexMap.map.{u, v, w, z} R J D L (a ≫ c)) i :=
  (congrArg (fun t => HomologicalComplex.homologyMap t i)
    (ComplexComposition.map.{u, v, w, z} R J D a b)).trans
      ((precomposed R J D a b c h i).trans
        (congrArg (fun t => HomologicalComplex.homologyMap t i)
          (ComplexComposition.map.{u, v, w, z} R J D a c).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.Homotopy
