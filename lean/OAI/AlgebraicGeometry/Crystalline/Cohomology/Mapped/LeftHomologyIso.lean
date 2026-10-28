import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # Left Homology Iso -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.LeftHomologyIso.MappedLeftHomologyIso

noncomputable section

/-! # Canonical homology transport agrees with mapped left homology data -/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (S : ShortComplex C) (d : S.LeftHomologyData)

theorem homologyIso : (S.mapHomologyIso F).hom ≫ F.map d.homologyIso.hom =
    (d.map F).homologyIso.hom := by
  let e : (S.map F).homology ≅ F.obj d.H := (d.map F).homologyIso
  have hm : S.mapHomologyIso F = e ≪≫ F.mapIso d.homologyIso.symm := d.mapHomologyIso_eq F
  rw [hm]
  change (e.hom ≫ (F.mapIso d.homologyIso).inv) ≫ (F.mapIso d.homologyIso).hom = e.hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.LeftHomologyIso.MappedLeftHomologyIso
