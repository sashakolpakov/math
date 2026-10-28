import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Refinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientChange

/-! # Refinement Coefficients -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.RefinementCoefficients

noncomputable section

/-! The actual signed ordered Cech refinement commutes with additive,
product-preserving changes of coefficients. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u vA uA vB uB
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G]
  (P : Cᵒᵖ ⥤ A)

private def fullObjectIso (n : ℕ) :
    G.obj ((Cech.TupleRestrictionFunctor.complex U P).X n) ≅
      (Cech.TupleRestrictionFunctor.complex U (P ⋙ G)).X n :=
  PreservesProduct.iso G (fun a : Fin (n+1) → ι => Cech.TupleRestrictionFunctor.factor U P a)

omit [LinearOrder ι] [G.Additive] in
private theorem full_projection (n : ℕ) (a : Fin (n+1) → ι) :
    (fullObjectIso U G P n).hom ≫ Cech.TupleRestrictionFunctor.projection U (P ⋙ G) a =
      G.map (Cech.TupleRestrictionFunctor.projection U P a) :=
  piComparison_comp_π G _ a

omit [Abelian A] [Abelian B] [G.Additive] in
private theorem ordered_projection (n : ℕ) (a : Projection.Index (ι := ι) n) :
    (AugmentedCech.CoefficientChange.objectIso U G P (n+1)).hom ≫
        Projection.projection U (P ⋙ G) n a =
      G.map (Projection.projection U P n a) :=
  piComparison_comp_π G _ a

omit [G.Additive] in
private theorem projection_natural (n : ℕ) :
    G.map (Projection.mapF U P n) ≫
        (AugmentedCech.CoefficientChange.objectIso U G P (n+1)).hom =
      (fullObjectIso U G P n).hom ≫ Projection.mapF U (P ⋙ G) n := by
  apply Pi.hom_ext
  intro (a : Projection.Index (ι := ι) n)
  change _ ≫ Projection.projection U (P ⋙ G) n a =
    _ ≫ Projection.projection U (P ⋙ G) n a
  rw [Category.assoc, ordered_projection, ← G.map_comp,
    Projection.mapF_projection, Category.assoc,
    Projection.mapF_projection, full_projection]

private abbrev sortedIndex {n : ℕ} (a : Fin (n+1) → ι) (ha : Function.Injective a) :
    Projection.Index (ι := ι) n :=
  ⟨a ∘ Tuple.sort a,
    (Tuple.monotone_sort a).strictMono_of_injective (ha.comp (Tuple.sort a).injective)⟩

private theorem sorted_subset {n : ℕ} (a : Fin (n+1) → ι) :
    Set.range (a ∘ Tuple.sort a) ⊆ Set.range a := by
  rintro x ⟨i, rfl⟩
  exact ⟨Tuple.sort a i, rfl⟩

private theorem inclusion_projection (n : ℕ) (a : Fin (n+1) → ι) (ha : Function.Injective a) :
    Retraction.inclusionF U P n ≫ Cech.TupleRestrictionFunctor.projection U P a =
      (Equiv.Perm.sign (Tuple.sort a) : ℤ) •
        (Projection.projection U P n (sortedIndex a ha) ≫
          Cech.TupleRestrictionFunctor.restriction U P a (a ∘ Tuple.sort a) (sorted_subset a)) := by
  rw [Retraction.inclusionF, Category.assoc,
    Cech.SortedProjection.projection_injective U P n a ha, comp_zsmul,
    Cech.TupleRestrictionFunctor.rowBasis_of_subset U P a _ (sorted_subset a),
    ← Category.assoc, Projection.zeroExtension_projection U P n _
      (sortedIndex a ha).property]

private theorem inclusion_projection_zero (n : ℕ) (a : Fin (n+1) → ι)
    (ha : ¬ Function.Injective a) :
    Retraction.inclusionF U P n ≫ Cech.TupleRestrictionFunctor.projection U P a = 0 := by
  rw [Retraction.inclusionF, Category.assoc,
    Cech.SortedProjection.projection_not_injective U P n a ha, comp_zero]

private theorem inclusion_natural (n : ℕ) :
    G.map (Retraction.inclusionF U P n) ≫ (fullObjectIso U G P n).hom =
      (AugmentedCech.CoefficientChange.objectIso U G P (n+1)).hom ≫
        Retraction.inclusionF U (P ⋙ G) n := by
  apply Pi.hom_ext
  intro (a : Fin (n+1) → ι)
  change _ ≫ Cech.TupleRestrictionFunctor.projection U (P ⋙ G) a =
    _ ≫ Cech.TupleRestrictionFunctor.projection U (P ⋙ G) a
  rw [Category.assoc, full_projection, ← G.map_comp, Category.assoc]
  by_cases ha : Function.Injective a
  · rw [inclusion_projection U P n a ha, inclusion_projection U (P ⋙ G) n a ha,
      Functor.map_zsmul, G.map_comp, comp_zsmul, ← Category.assoc, ordered_projection]
    rfl
  · rw [inclusion_projection_zero U P n a ha, inclusion_projection_zero U (P ⋙ G) n a ha,
      G.map_zero, comp_zero]

variable [HasCoproducts.{0} A] [HasCoproducts.{0} B]

omit [LinearOrder ι] [LinearOrder κ] [G.Additive] [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
private theorem full_refinement_natural (n : ℕ) :
    G.map ((GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r P).f n) ≫ (fullObjectIso V G P n).hom =
      (fullObjectIso U G P n).hom ≫ (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (P ⋙ G)).f n := by
  let En := (NonemptyCechNerve.nerve U).obj (op (SimplexCategory.mk n))
  let Em := (NonemptyCechNerve.nerve V).obj (op (SimplexCategory.mk n))
  let a := (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.nerveMap U V r).app (op (SimplexCategory.mk n))
  exact AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.piComparison_natural G
    (fun i : En.I => P.obj (op (En.obj i))) (fun i : Em.I => P.obj (op (Em.obj i)))
    a.f (fun i => P.map (a.φ i).op)

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
theorem complex_natural :
    (G.mapHomologicalComplex (.up ℕ)).map (Refinement.map U V r P) ≫
        (CoefficientChange.complexIso V G P).hom =
      (CoefficientChange.complexIso U G P).hom ≫
        Refinement.map U V r (P ⋙ G) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change G.map (Retraction.inclusionF U P n ≫
      (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r P).f n ≫ Projection.mapF V P n) ≫
      (AugmentedCech.CoefficientChange.objectIso V G P (n+1)).hom =
    (AugmentedCech.CoefficientChange.objectIso U G P (n+1)).hom ≫
      (Retraction.inclusionF U (P ⋙ G) n ≫
        (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (P ⋙ G)).f n ≫
          Projection.mapF V (P ⋙ G) n)
  simp only [G.map_comp, Category.assoc]
  rw [projection_natural, ← Category.assoc (G.map ((GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r P).f n)),
    full_refinement_natural, Category.assoc,
    ← Category.assoc (G.map (Retraction.inclusionF U P n)), inclusion_natural]
  simp only [Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.RefinementCoefficients
