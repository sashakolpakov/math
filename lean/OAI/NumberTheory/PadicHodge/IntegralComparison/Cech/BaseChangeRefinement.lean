import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.FamilyRefinement

/-! # Base Change Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BaseChangeRefinement

noncomputable section

/-! Inverse-image Čech comparisons respect literal refinements of
covering families, including the actual presheaf transfer. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v vD vA u uD uA
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A]
  {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasFiniteProducts D]
  (F : C ⥤ D) [PreservesFiniteLimits F] {ι κ : Type w}
  (U : ι → C) (V : κ → C) (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

def refinement : FormalCoproduct.mk κ (F.obj ∘ V) ⟶ FormalCoproduct.mk ι (F.obj ∘ U) where
  f := r.f
  φ j := F.map (r.φ j)

theorem naturality (P : Dᵒᵖ ⥤ A) :
    GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) r
        (F.op ⋙ P) ≫ (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F V P).hom =
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).hom ≫
        GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι (F.obj ∘ U))
          (FormalCoproduct.mk κ (F.obj ∘ V)) (refinement F U V r) P := by
  apply HomologicalComplex.Hom.ext
  funext n
  let a := (FormalCoproduct.cechFunctor.map r).app (op ⦋n⦌)
  let b := (FormalCoproduct.cechFunctor.map (refinement F U V r)).app (op ⦋n⦌)
  apply AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.productIso_natural
    (fun t => P.mapIso (PreservesProduct.iso F (U ∘ t)).symm.op)
    (fun t => P.mapIso (PreservesProduct.iso F (V ∘ t)).symm.op)
    a.f (fun t => P.map (F.map (a.φ t)).op) (fun t => P.map (b.φ t).op)
  intro t
  change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
  exact (P.map_comp _ _).symm.trans
    ((congrArg P.map (Subsingleton.elim _ _)).trans (P.map_comp _ _))

theorem inverse (P : Dᵒᵖ ⥤ A) :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).inv ≫
        GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) r
          (F.op ⋙ P) =
      GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι (F.obj ∘ U))
        (FormalCoproduct.mk κ (F.obj ∘ V)) (refinement F U V r) P ≫
          (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F V P).inv := by
  apply (cancel_epi (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← naturality]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem transfer {P : Dᵒᵖ ⥤ A} {Q : Cᵒᵖ ⥤ A} (a : F.op ⋙ P ⟶ Q) :
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).inv ≫ (cechComplexFunctor U).map a) ≫
        GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) r Q =
      GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι (F.obj ∘ U))
        (FormalCoproduct.mk κ (F.obj ∘ V)) (refinement F U V r) P ≫
          ((AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F V P).inv ≫ (cechComplexFunctor V).map a) := by
  have h := GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.naturality
    (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) r a
  change (cechComplexFunctor U).map a ≫
      GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) r Q =
    GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) r
      (F.op ⋙ P) ≫ (cechComplexFunctor V).map a at h
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).inv ≫ z) h).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (cechComplexFunctor V).map a) (inverse F U V r P)).trans
          (Category.assoc _ _ _))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BaseChangeRefinement
