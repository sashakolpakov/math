import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.SingleFunctorCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafCover

/-! # Presheaf Single Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafSingleCoordinates

noncomputable section

/-! The original principal-to-cover comparison on a single coefficient
has the literal unshifted Čech comparison in its canonical total
coordinates. Both inverse refinement maps are retained. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

private theorem isIso_of_square {C : Type*} [Category* C]
    {A B A' B' : C} (a : A ⟶ B) (b : A' ⟶ B') (e : A ≅ A') (f : B ≅ B')
    [IsIso a] (h : a ≫ f.hom = e.hom ≫ b) : IsIso b := by
  have hb : b = e.inv ≫ a ≫ f.hom := by
    rw [h, Iso.inv_hom_id_assoc]
  rw [hb]
  infer_instance

private theorem inverse_square {C : Type*} [Category* C]
    {A B A' B' : C} (a : A ⟶ B) (b : A' ⟶ B') (e : A ≅ A') (f : B ≅ B')
    [IsIso a] [IsIso b] (h : a ≫ f.hom = e.hom ≫ b) :
    inv a ≫ e.hom = f.hom ≫ inv b := by
  apply (cancel_mono b).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h, IsIso.inv_hom_id_assoc]

private theorem horizontal {C : Type*} [Category* C]
    {A B E A' B' E' : C} {f : A ⟶ B} {g : B ⟶ E}
    {a : A ⟶ A'} {b : B ⟶ B'} {e : E ⟶ E'}
    {f' : A' ⟶ B'} {g' : B' ⟶ E'}
    (hf : f ≫ b = a ≫ f') (hg : g ≫ e = b ≫ g') :
    (f ≫ g) ≫ e = a ≫ f' ≫ g' := by
  rw [Category.assoc, hg, ← Category.assoc f b, hf, Category.assoc]

variable {X : TopCat.{u}} {D : Type v} [Category D] [Abelian D]
  [HasProducts.{u} D] [HasCoproducts.{0} D]
  (P : (Opens X)ᵒᵖ ⥤ D) (c g : ℕ)

section Refinement
variable (A : Opens X) {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → Opens X) (V : κ → Opens X)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

theorem relative_isIso
    [IsIso (RelativeCech.Refinement.homology A U V r
      ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) c).obj P) (g+c))] :
    IsIso (homologyMap (AugmentedOrdered.CechRefinement.map U V r
      ((RelativeCech.Intersections.intersect A).op ⋙ P)) g) :=
  isIso_of_square _ _ (Functor.SingleTotal.homologyIso (RelativeCech.Total.localFunctor A U) P c g)
    (Functor.SingleTotal.homologyIso (RelativeCech.Total.localFunctor A V) P c g)
    (Cech.SingleFunctorCoordinates.relative P c g A U V r)

theorem ordered_isIso
    [IsIso (homologyMap (OrderedCech.Refinement.totalMap U V r
      ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) c).obj P)) (g+c))] :
    IsIso (homologyMap (OrderedCech.Refinement.map U V r P) g) :=
  isIso_of_square _ _ (Functor.SingleTotal.homologyIso (OrderedCech.Functor.Projection.functor U) P c g)
    (Functor.SingleTotal.homologyIso (OrderedCech.Functor.Projection.functor V) P c g)
    (Cech.SingleFunctorCoordinates.ordered P c g U V r)
end Refinement

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X)
  {ι κ ν μ ρ : Type u}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  (B : κ → Opens X) (J : ν → Opens X)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s
    ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) c).obj P) (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) c).obj P)) (g+c))]

def coefficientComparison :
    (AugmentedOrdered.Cech.complex W (F.op ⋙ P)).homology g ⟶
      (OrderedCech.Projection.complex V P).homology g := by
  letI := relative_isIso P c g (F.obj (⊤_ C)) B J s
  letI := ordered_isIso P c g V T t
  exact homologyMap (AugmentedCech.AmbientCoordinates.iso F W P).hom g ≫
    homologyMap (AugmentedOrdered.CechRefinement.map (F.obj ∘ W) J r
      ((RelativeCech.Intersections.intersect (F.obj (⊤_ C))).op ⋙ P)) g ≫
    inv (homologyMap (AugmentedOrdered.CechRefinement.map B J s
      ((RelativeCech.Intersections.intersect (F.obj (⊤_ C))).op ⋙ P)) g) ≫
    homologyMap ((RelativeCech.Total.comparison (F.obj (⊤_ C)) B).app P) g ≫
    homologyMap (OrderedCech.Refinement.map (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B) T l P) g ≫
    inv (homologyMap (OrderedCech.Refinement.map V T t P) g)

theorem comparison :
    PresheafCover.Comparison.comparison F W B J r s V T l t
      ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) c).obj P) (g+c) ≫
        (Functor.SingleTotal.homologyIso (OrderedCech.Functor.Projection.functor V) P c g).hom =
      (Functor.SingleTotal.homologyIso (Cech.SingleFunctorCoordinates.localFunctor F W) P c g).hom ≫
        coefficientComparison P c g F W B J r s V T l t := by
  let := relative_isIso P c g (F.obj (⊤_ C)) B J s
  let := ordered_isIso P c g V T t
  have ha := Cech.SingleFunctorCoordinates.ambient P c g F W
  have hr := Cech.SingleFunctorCoordinates.relative P c g (F.obj (⊤_ C)) (F.obj ∘ W) J r
  have hs := Cech.SingleFunctorCoordinates.relative P c g (F.obj (⊤_ C)) B J s
  have hsi := inverse_square _ _
    (Functor.SingleTotal.homologyIso (RelativeCech.Total.localFunctor (F.obj (⊤_ C)) B) P c g)
    (Functor.SingleTotal.homologyIso (RelativeCech.Total.localFunctor (F.obj (⊤_ C)) J) P c g) hs
  have hd := Cech.SingleFunctorCoordinates.extension P c g (F.obj (⊤_ C)) B
  have hl := Cech.SingleFunctorCoordinates.ordered P c g (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B) T l
  have ht := Cech.SingleFunctorCoordinates.ordered P c g V T t
  have hti := inverse_square _ _ (Functor.SingleTotal.homologyIso (OrderedCech.Functor.Projection.functor V) P c g)
    (Functor.SingleTotal.homologyIso (OrderedCech.Functor.Projection.functor T) P c g) ht
  have h := horizontal (horizontal (horizontal (horizontal (horizontal ha hr) hsi) hd) hl) hti
  simpa only [PresheafCover.Comparison.comparison,
    Relative.PresheafCommonRefinement.comparison,
    Presheaf.OrderedCover.Comparison.comparison, coefficientComparison,
    homologyMapIso_hom, Category.assoc] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafSingleCoordinates
