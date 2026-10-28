import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedMonoidHomEquations

/-! # Monoidal Product Comparison Unit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidalProductComparisonUnit

noncomputable section

/-! The inverse product comparison of a strong monoidal functor preserves the actual monoid unit. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem monoidalProductComparison_inv_preserves_unit
    {S T : Scheme.{u}} (F : Over S ⥤ Over T) [F.Monoidal]
    (A B : Over S) [MonObj A] [MonObj B] :
    η[F.obj (A ⊗ B)] ≫ (Functor.Monoidal.μIso F A B).inv = η[F.obj A ⊗ F.obj B] := by
  let e := Functor.Monoidal.μIso F A B
  have hfst : e.inv ≫ fst (F.obj A) (F.obj B) = F.map (fst A B) := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    exact (Functor.Monoidal.μ_fst F A B).symm
  have hsnd : e.inv ≫ snd (F.obj A) (F.obj B) = F.map (snd A B) := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    exact (Functor.Monoidal.μ_snd F A B).symm
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, hfst, IsMonHom.one_hom (fst (F.obj A) (F.obj B))]
    exact (MappedMonoidHomEquations.mappedMonoidHom_one_iff F (fst A B)).mpr (congrArg F.map (IsMonHom.one_hom (fst A B)))
  · rw [Category.assoc, hsnd, IsMonHom.one_hom (snd (F.obj A) (F.obj B))]
    exact (MappedMonoidHomEquations.mappedMonoidHom_one_iff F (snd A B)).mpr (congrArg F.map (IsMonHom.one_hom (snd A B)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidalProductComparisonUnit
