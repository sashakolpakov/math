import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology

/-! # Complex Homology Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomologyNaturality.MappedComplexHomologyNaturality

noncomputable section

/-! # Naturality of canonical homology transport for mapped complexes -/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  {K L : CochainComplex C ℕ} (f : K ⟶ L)

theorem naturality (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map f) n ≫
      (ComplexHomology.MappedComplexHomology.iso F L n).hom =
    (ComplexHomology.MappedComplexHomology.iso F K n).hom ≫ F.map (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor C (.up ℕ) n).map f) F

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomologyNaturality.MappedComplexHomologyNaturality
