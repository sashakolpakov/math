import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.SingleFunctorCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.EdgeRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalProjection

/-! # Single Global Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.SingleGlobalSource

noncomputable section

/-! A genuine single-to-complex map gives the same global source map
on covers related by an actual common refinement. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inverse_coordinates {C : Type*} [Category C]
    {A B A' B' : C} (e : A ≅ A') (f : B ≅ B')
    (r : A ⟶ B) (s : A' ⟶ B') (h : r ≫ f.hom = e.hom ≫ s) :
    e.inv ≫ r = s ≫ f.inv := by
  apply (cancel_mono f.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

private theorem inverse_edge {C : Type*} [Category C]
    {A B Z : C} (e : Z ⟶ A) (f : Z ⟶ B) [IsIso e] [IsIso f]
    (r : A ⟶ B) (h : e ≫ r = f) : r ≫ inv f = inv e := by
  apply (cancel_epi e).mp
  rw [← Category.assoc, h, IsIso.hom_inv_id, IsIso.hom_inv_id]

private theorem descend {C : Type*} [Category C]
    {A B A' B' M N Z : C} (e : A ≅ A') (f : B ≅ B')
    (r : A ⟶ B) (s : A' ⟶ B') (a : A ⟶ M) (b : B ⟶ N) (t : M ⟶ N)
    (j : Z ⟶ M) (k : Z ⟶ N) [IsIso j] [IsIso k]
    (hc : r ≫ f.hom = e.hom ≫ s) (ha : a ≫ t = r ≫ b) (he : j ≫ t = k) :
    e.inv ≫ a ≫ inv j = s ≫ f.inv ≫ b ≫ inv k := by
  have hc' := inverse_coordinates e f r s hc
  have he' := inverse_edge j k t he
  calc
    e.inv ≫ a ≫ inv j = e.inv ≫ a ≫ t ≫ inv k := by rw [he']
    _ = (e.inv ≫ r) ≫ b ≫ inv k := by rw [← Category.assoc a t, ha]; simp only [Category.assoc]
    _ = s ≫ f.inv ≫ b ≫ inv k := by rw [hc']; simp only [Category.assoc]

universe u v
variable {X : TopCat.{u}} {D : Type v} [Category D] [Abelian D]
  [HasProducts.{u} D] [HasCoproducts.{0} D]
  (P : (Opens X)ᵒᵖ ⥤ D) (g : ℕ)
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ)
  (a : (single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) g).obj P ⟶ K)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → Opens X) (V : κ → Opens X)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

abbrev totalMap := (OrderedCech.TotalProjection.ordered U).map a
abbrev sourceIso := Functor.SingleTotal.homologyIso (OrderedCech.Functor.Projection.functor U) P g g
abbrev edgeMap := homologyMap (Presheaf.OrderedCechEdge.edge U K) (g+g)

variable [IsIso (edgeMap g K U)]

def map : (OrderedCech.Projection.complex U P).homology g ⟶
    (Presheaf.OrderedCechEdge.sections K).homology (g+g) :=
  (sourceIso P g U).inv ≫ homologyMap (totalMap P g K a U) (g+g) ≫ inv (edgeMap g K U)

def mapDouble : (OrderedCech.Projection.complex U P).homology g ⟶
    (Presheaf.OrderedCechEdge.sections K).homology (2*g) :=
  SingleGlobalSource.map P g K a U ≫ eqToHom (congrArg (fun q =>
    (Presheaf.OrderedCechEdge.sections K).homology q) (Nat.two_mul g).symm)

omit [IsIso (edgeMap g K U)] in
theorem total_naturality : totalMap P g K a U ≫ OrderedCech.Refinement.totalMap U V r K =
    OrderedCech.Refinement.totalMap U V r
      ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) g).obj P) ≫ totalMap P g K a V := by
  let T := HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map ((NatTrans.mapHomologicalComplex
      (OrderedCech.Refinement.transformation U V r) (.up ℕ)).naturality a)).trans
        (T.map_comp _ _))

omit [IsIso (edgeMap g K U)] in
theorem homology_naturality :
    homologyMap (totalMap P g K a U) (g+g) ≫
      homologyMap (OrderedCech.Refinement.totalMap U V r K) (g+g) =
    homologyMap (OrderedCech.Refinement.totalMap U V r
      ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) g).obj P)) (g+g) ≫
      homologyMap (totalMap P g K a V) (g+g) :=
  (homologyMap_comp _ _ (g+g)).symm.trans
    ((congrArg (fun f => homologyMap f (g+g)) (total_naturality P g K a U V r)).trans
      (homologyMap_comp _ _ (g+g)))

variable [IsIso (edgeMap g K V)]

theorem refinement : SingleGlobalSource.map P g K a U =
    homologyMap (OrderedCech.Refinement.map U V r P) g ≫ SingleGlobalSource.map P g K a V :=
  descend (sourceIso P g U) (sourceIso P g V)
    (homologyMap (OrderedCech.Refinement.totalMap U V r
      ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) g).obj P)) (g+g))
    (homologyMap (OrderedCech.Refinement.map U V r P) g)
    (homologyMap (totalMap P g K a U) (g+g))
    (homologyMap (totalMap P g K a V) (g+g))
    (homologyMap (OrderedCech.Refinement.totalMap U V r K) (g+g))
    (edgeMap g K U) (edgeMap g K V)
    (Cech.SingleFunctorCoordinates.ordered P g g U V r)
    (homology_naturality P g K a U V r)
    (OrderedCech.EdgeRefinement.homology U V r K (g+g))

variable (T : ν → Opens X)
  (rU : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι U)
  (rV : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk κ V)
  [IsIso (edgeMap g K T)]
  [IsIso (homologyMap (OrderedCech.Refinement.map V T rV P) g)]

def coefficientComparison : (OrderedCech.Projection.complex U P).homology g ⟶
    (OrderedCech.Projection.complex V P).homology g :=
  homologyMap (OrderedCech.Refinement.map U T rU P) g ≫
    inv (homologyMap (OrderedCech.Refinement.map V T rV P) g)

theorem common_refinement : SingleGlobalSource.map P g K a U =
    coefficientComparison P g U V T rU rV ≫ SingleGlobalSource.map P g K a V := by
  calc
    SingleGlobalSource.map P g K a U = homologyMap (OrderedCech.Refinement.map U T rU P) g ≫
        SingleGlobalSource.map P g K a T := refinement P g K a U T rU
    _ = coefficientComparison P g U V T rU rV ≫ SingleGlobalSource.map P g K a V := by
      rw [coefficientComparison, refinement P g K a V T rV]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]

theorem common_refinementDouble : mapDouble P g K a U =
    coefficientComparison P g U V T rU rV ≫ mapDouble P g K a V := by
  simpa only [mapDouble, Category.assoc] using
    congrArg (fun f => f ≫ eqToHom (congrArg (fun q =>
      (Presheaf.OrderedCechEdge.sections K).homology q) (Nat.two_mul g).symm))
      (common_refinement P g K a U V T rU rV)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.SingleGlobalSource
