import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexNaturality

/-! # Complex Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexComposition

noncomputable section

/-! Canonical constant-module section maps respect postcomposition on actual complexes. -/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max w z} (Sheaf J (ModuleCat.{w} R))]
  (D : CochainComplex (ModuleCat.{w} R) ℕ)
  {K L : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ}
  (a : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℕ)).obj D ⟶ K)
  (b : K ⟶ L)

theorem component (n : ℕ) : (ComplexMap.map R J D L (a ≫ b)).f n =
    (ComplexMap.map R J D K a).f n ≫
      (Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0).map (b.f n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hc : (constantSheaf J (ModuleCat.{w} R)).map (𝟙 (D.X n)) ≫ (a.f n ≫ b.f n) = a.f n ≫ b.f n := by
    rw [(constantSheaf J (ModuleCat.{w} R)).map_id, Category.id_comp]
  exact (Module.ConstantSections.section_natural R J (𝟙 (D.X n)) (b.f n)
    (a.f n) (a.f n ≫ b.f n) hc x.down).symm

theorem map : ComplexMap.map R J D L (a ≫ b) =
    ComplexMap.map R J D K a ≫
      ((Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0).mapHomologicalComplex
        (.up ℕ)).map b := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact component R J D a b n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexComposition
