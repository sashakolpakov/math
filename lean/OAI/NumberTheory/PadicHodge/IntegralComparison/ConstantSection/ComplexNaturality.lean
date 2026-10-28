import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexMap

/-! # Complex Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexNaturality

noncomputable section

/-!
# IntegralComparison: the canonical complex section map is natural in its source and target
-/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max w z} (Sheaf J (ModuleCat.{w} R))]
  {D D' : CochainComplex (ModuleCat.{w} R) ℕ}
  {K K' : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ}
  (g : D ⟶ D') (h : K ⟶ K')
  (a : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (ComplexShape.up ℕ)).obj D ⟶ K)
  (a' : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (ComplexShape.up ℕ)).obj D' ⟶ K')
  (hc : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (ComplexShape.up ℕ)).map g ≫ a' = a ≫ h)

include hc in
theorem naturality : ComplexMap.map R J D K a ≫
    ((Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0).mapHomologicalComplex
      (ComplexShape.up ℕ)).map h =
    ((ModuleCat.uliftFunctor.{z, w} R).mapHomologicalComplex (ComplexShape.up ℕ)).map g ≫
      ComplexMap.map R J D' K' a' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hn : (constantSheaf J (ModuleCat.{w} R)).map (g.f n) ≫ a'.f n = a.f n ≫ h.f n :=
    congrArg (fun q => q.f n) hc
  exact Module.ConstantSections.section_natural R J (g.f n) (h.f n) (a.f n) (a'.f n) hn x.down

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexNaturality
