import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.LeftHomologyIso

/-! # Complex Homology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology

noncomputable section

/-! # Canonical homology transport for mapped complexes and adjacent terms -/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  (K : CochainComplex C ℕ)

def iso (n : ℕ) : ((F.mapHomologicalComplex (.up ℕ)).obj K).homology n ≅ F.obj (K.homology n) :=
  (K.sc n).mapHomologyIso F

theorem shortIso (i j k : ℕ) (hi : (ComplexShape.up ℕ).prev j = i)
    (hk : (ComplexShape.up ℕ).next j = k) :
    (iso F K j).hom ≫ F.map (K.homologyIsoSc' i j k hi hk).hom =
      (((F.mapHomologicalComplex (.up ℕ)).obj K).homologyIsoSc' i j k hi hk).hom ≫
        ((K.sc' i j k).mapHomologyIso F).hom := by
  subst i
  subst k
  simp only [HomologicalComplex.homologyIsoSc'_eq_refl, Iso.refl_hom]
  let e := iso F K j
  change e.hom ≫ F.map (𝟙 (K.homology j)) = 𝟙 _ ≫ e.hom
  rw [F.map_id, Category.comp_id, Category.id_comp]

theorem adjacent (n : ℕ) :
    (iso F K (n + 1)).hom ≫ F.map (K.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom =
      (((F.mapHomologicalComplex (.up ℕ)).obj K).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom ≫
        ((K.sc' n (n + 1) (n + 2)).mapHomologyIso F).hom :=
  shortIso F K n (n + 1) (n + 2) (by simp) (by simp)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology
