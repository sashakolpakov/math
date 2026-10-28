import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Reindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleReindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BaseChangeRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Refinement

/-! # Reindex Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexRefinement

noncomputable section

/-! The original signed-sorting inclusion and ordered refinement
commute with finite-limit-preserving changes of open diagrams. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteLimits r]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A]
  (P : Dᵒᵖ ⥤ A)

theorem inclusion :
    (Reindex.iso r U P).hom ≫ Retraction.inclusion (r.obj ∘ U) P =
      Retraction.inclusion U (r.op ⋙ P) ≫ (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso r U P).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_epi (Projection.mapF U (r.op ⋙ P) n)).mp
  have hp := congrArg (fun z => z.f n) (Reindex.projection r U P)
  change (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.componentIso r U P ⦋n⦌).hom ≫
      Projection.mapF (r.obj ∘ U) P n =
    Projection.mapF U (r.op ⋙ P) n ≫ (Reindex.iso r U P).hom.f n at hp
  change Projection.mapF U (r.op ⋙ P) n ≫
      ((Reindex.iso r U P).hom.f n ≫ Retraction.inclusionF (r.obj ∘ U) P n) =
    Projection.mapF U (r.op ⋙ P) n ≫
      (Retraction.inclusionF U (r.op ⋙ P) n ≫
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.componentIso r U P ⦋n⦌).hom)
  rw [← Category.assoc, ← hp, Category.assoc, Retraction.mapF_inclusionF,
    ← Category.assoc, Retraction.mapF_inclusionF]
  exact Cech.TupleReindex.map_naturality r U P (AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternation.cechTupleAlternatingProjection n)
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n)

variable [HasCoproducts.{0} A]
  {κ : Type u} [LinearOrder κ] (V : κ → C)
  (ρ : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

omit [HasCoproducts A] in
theorem refinement :
    Refinement.map U V ρ (r.op ⋙ P) ≫ (Reindex.iso r V P).hom =
      (Reindex.iso r U P).hom ≫ Refinement.map (r.obj ∘ U) (r.obj ∘ V)
        (Cech.BaseChangeRefinement.refinement r U V ρ) P := by
  have hi := inclusion r U P
  have hr := Cech.BaseChangeRefinement.naturality r U V ρ P
  change GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V ρ (r.op ⋙ P) ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso r V P).hom =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso r U P).hom ≫
      GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map (r.obj ∘ U) (r.obj ∘ V)
        (Cech.BaseChangeRefinement.refinement r U V ρ) P at hr
  rw [Refinement.map_eq, Refinement.map_eq]
  simp only [Category.assoc]
  rw [← Reindex.projection r V P]
  rw [← Category.assoc (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V ρ (r.op ⋙ P)), hr]
  simp only [Category.assoc]
  rw [← Category.assoc (Retraction.inclusion U (r.op ⋙ P)), ← hi]
  simp only [Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexRefinement
