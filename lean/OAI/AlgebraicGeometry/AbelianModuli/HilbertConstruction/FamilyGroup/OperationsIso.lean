import OAI.CategoryTheory.Isomorphisms.IsoConjugateMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyOperationData

/-! # Operations Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup

noncomputable section

/-! Group laws on actual family operations are invariant under a specified isomorphism of the underlying family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.BraidedCategory

universe u

variable {S : Scheme.{u}} {X Y : Over S} (D : Operations.FamilyGroupOperations X) (e : X ≅ Y)

def Operations.FamilyGroupOperations.ofIso : Operations.FamilyGroupOperations Y where
  unit := D.unit ≫ e.hom
  mul := CategoryTheory.Isomorphisms.IsoConjugateMap.isoConjugateMap (tensorIso e e) e D.mul
  inv := CategoryTheory.Isomorphisms.IsoConjugateMap.isoConjugateMap e e D.inv

theorem Operations.FamilyGroupOperations.ofIso_laws (h : D.Laws) : (D.ofIso e).Laws := by
  let : GrpObj X := D.groupObj h
  let : GrpObj Y := GrpObj.ofIso e
  refine ⟨MonObj.one_mul Y, MonObj.mul_one Y, MonObj.mul_assoc Y,
    GrpObj.left_inv Y, GrpObj.right_inv Y, ?_⟩
  change (β_ Y Y).hom ≫ ((e.inv ⊗ₘ e.inv) ≫ D.mul ≫ e.hom) =
    (e.inv ⊗ₘ e.inv) ≫ D.mul ≫ e.hom
  rw [← Category.assoc, ← braiding_naturality, Category.assoc,
    ← Category.assoc (β_ X X).hom, h.mul_comm]

theorem Operations.FamilyGroupOperations.ofIso_symm : (D.ofIso e).ofIso e.symm = D := by
  apply Operations.FamilyGroupOperations.ext
  · dsimp only [Operations.FamilyGroupOperations.ofIso, CategoryTheory.Isomorphisms.IsoConjugateMap.isoConjugateMap, tensorIso_inv, Iso.symm_hom]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · dsimp only [Operations.FamilyGroupOperations.ofIso, CategoryTheory.Isomorphisms.IsoConjugateMap.isoConjugateMap, tensorIso_inv, Iso.symm_hom, Iso.symm_inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id, id_tensorHom_id, Category.id_comp]
  · dsimp only [Operations.FamilyGroupOperations.ofIso, CategoryTheory.Isomorphisms.IsoConjugateMap.isoConjugateMap, tensorIso_inv, Iso.symm_hom, Iso.symm_inv]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

theorem Operations.FamilyGroupOperations.ofIso_laws_iff : (D.ofIso e).Laws ↔ D.Laws := by
  constructor
  · intro h
    have hh := (D.ofIso e).ofIso_laws e.symm h
    rwa [D.ofIso_symm e] at hh
  · exact D.ofIso_laws e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup
