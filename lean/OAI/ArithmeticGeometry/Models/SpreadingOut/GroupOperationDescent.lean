import OAI.ArithmeticGeometry.Models.SpreadingOut.GenericMorphisms
import OAI.ArithmeticGeometry.Models.SpreadingOut.GroupBaseChange
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Group Operation Descent -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GroupOperationDescent.Construction

noncomputable section

/-! The multiplication, identity, and inverse maps descend over one larger
finite coefficient base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.CategoryTheory.Functor
open scoped _root_.NumberField

universe u

def groupOperationObjects {S : Scheme.{u}} (M : Over S) : Fin 3 → Over S :=
  ![𝟙_ _, M, M ⊗ M]

def groupOperationSources : Fin 3 → Fin 3 := ![0, 2, 1]

theorem groupOperationObjects_finitePresentation
    {S : Scheme.{u}} (M : Over S) [Smooth M.hom] [IsProper M.hom] (i : Fin 3) :
    Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (groupOperationObjects M i).hom := by
  fin_cases i <;> dsimp [groupOperationObjects] <;>
    exact ⟨inferInstance, inferInstance, inferInstance⟩

def groupOperationMaps
    {S T : Scheme.{u}} (H : Over S ⥤ Over T) [H.Monoidal]
    (M : Over S) [GrpObj (H.obj M)] :
    ∀ j : Fin 3, H.obj (groupOperationObjects M (groupOperationSources j)) ⟶
      H.obj (groupOperationObjects M 1) :=
  Fin.cases (OplaxMonoidal.η H ≫ η[H.obj M])
    (Fin.cases (OplaxMonoidal.δ H M M ≫ μ[H.obj M])
      (Fin.cases ι[H.obj M] (fun i ↦ Fin.elim0 i)))

theorem group_operations_descend_raw
    {K : Type u} [Field K] {s : Finset K}
    (M : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) [Smooth M.hom] [IsProper M.hom]
    [GrpObj ((Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj M)] :
    ∃ (t : Finset K) (h : s ⊆ t),
      let F := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
      let G := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)
      let H := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
      let c := GenericMorphisms.Construction.coefficientGenericComparison h
      ∃ (a : F.obj (𝟙_ _) ⟶ F.obj M) (b : F.obj (M ⊗ M) ⟶ F.obj M)
        (d : F.obj M ⟶ F.obj M),
        (G.map a ≫ (c.app M).hom = (c.app (𝟙_ _)).hom ≫ OplaxMonoidal.η H ≫ η[H.obj M]) ∧
        (G.map b ≫ (c.app M).hom = (c.app (M ⊗ M)).hom ≫ OplaxMonoidal.δ H M M ≫ μ[H.obj M]) ∧
        (G.map d ≫ (c.app M).hom = (c.app M).hom ≫ ι[H.obj M]) := by
  let H := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
  obtain ⟨t, h, b, hb⟩ := GenericMorphisms.Construction.finite_generic_morphisms_descend (groupOperationObjects M)
    (groupOperationObjects_finitePresentation M) groupOperationSources (fun _ ↦ 1)
    (groupOperationMaps H M)
  exact ⟨t, h, b 0, b 1, b 2, hb 0, hb 1, hb 2⟩

theorem group_operations_descend
    {K : Type u} [Field K] {s : Finset K}
    (M : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) [Smooth M.hom] [IsProper M.hom]
    [GrpObj ((Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj M)] :
    ∃ (t : Finset K) (h : s ⊆ t),
      let F := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
      let G := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)
      let c := GenericMorphisms.Construction.coefficientGenericComparison h
      let N := F.obj M
      letI : GrpObj (G.obj N) := GrpObj.ofIso (c.app M).symm
      ∃ (one : 𝟙_ (Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K t)) ⟶ N)
        (mul : N ⊗ N ⟶ N) (inv : N ⟶ N),
        G.map one = OplaxMonoidal.η G ≫ η[G.obj N] ∧
        G.map mul = OplaxMonoidal.δ G N N ≫ μ[G.obj N] ∧
        G.map inv = ι[G.obj N] := by
  let H := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
  obtain ⟨t, h, a, b, d, ha, hb, hd⟩ := group_operations_descend_raw M
  let F := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
  let G := Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)
  let c := GenericMorphisms.Construction.coefficientGenericComparison h
  refine ⟨t, h, LaxMonoidal.ε F ≫ a, LaxMonoidal.μ F M M ≫ b, d, ?_, ?_, ?_⟩
  · exact GroupBaseChange.Construction.descended_one_image F G H c M a ha
  · exact GroupBaseChange.Construction.descended_mul_image F G H c M b hb
  · exact GroupBaseChange.Construction.descended_inv_image F G H c M d hd

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GroupOperationDescent.Construction
