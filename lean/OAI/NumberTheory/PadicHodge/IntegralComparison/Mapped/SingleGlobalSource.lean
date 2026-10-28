import OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.SingleGlobalSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.MappedSingleCoordinates

/-! # Single Global Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleGlobalSource

noncomputable section

/-! Globalizing an actual mapped single-sheaf complex uses the same
original single coordinates on every affine cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inverse_coordinates {C : Type*} [Category C] {A B D : C}
    (t : A ≅ B) (p : B ≅ D) (o : A ≅ D) (h : t.hom ≫ p.hom = o.hom) :
    o.inv = p.inv ≫ t.inv := by
  have hi : t ≪≫ p = o := Iso.ext h
  exact (congrArg Iso.inv hi).symm

universe u v w z
variable {X : TopCat.{u}} {D : Type v} [Category D] [Abelian D]
  [HasProducts.{u} D] [HasCoproducts.{0} D]
  {C : Type w} [Category.{z} C] [Abelian C]
  (J : C ⥤ (Opens X)ᵒᵖ ⥤ D) [J.Additive] (M : C) (g : ℕ)
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ)
  (a : (J.mapHomologicalComplex (.up ℕ)).obj ((single C (.up ℕ) g).obj M) ⟶ K)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → Opens X) (V : κ → Opens X)

abbrev singleIso := (singleMapHomologicalComplex J (.up ℕ) g).app M
abbrev plainMap := (singleIso J M g).inv ≫ a
abbrev originalIso := IntegralComparison.Functor.SingleTotal.homologyIso (J ⋙ OrderedCech.Functor.Projection.functor U) M g g

def totalIso := (OrderedCech.TotalProjection.ordered U).mapIso (singleIso J M g)

theorem coordinates :
    (homologyMapIso (totalIso J M g U) (g+g)).hom ≫
      (Ordered.SingleGlobalSource.sourceIso (J.obj M) g U).hom =
    (originalIso J M g U).hom :=
  IntegralComparison.Functor.MappedSingleCoordinates.comparison J (OrderedCech.Functor.Projection.functor U) M g g

variable [IsIso (Ordered.SingleGlobalSource.edgeMap g K U)]

def map : (OrderedCech.Projection.complex U (J.obj M)).homology g ⟶
    (Presheaf.OrderedCechEdge.sections K).homology (g+g) :=
  (originalIso J M g U).inv ≫
    homologyMap ((OrderedCech.TotalProjection.ordered U).map a) (g+g) ≫
      inv (Ordered.SingleGlobalSource.edgeMap g K U)

theorem map_eq : SingleGlobalSource.map J M g K a U =
    Ordered.SingleGlobalSource.map (J.obj M) g K (plainMap J M g K a) U := by
  have hi := inverse_coordinates (homologyMapIso (totalIso J M g U) (g+g))
    (Ordered.SingleGlobalSource.sourceIso (J.obj M) g U) (originalIso J M g U)
    (coordinates J M g U)
  dsimp only [SingleGlobalSource.map, Ordered.SingleGlobalSource.map, Ordered.SingleGlobalSource.totalMap,
    plainMap]
  rw [Functor.map_comp, homologyMap_comp, hi]
  simp only [Category.assoc]
  rfl

theorem coordinates_map :
    (originalIso J M g U).hom ≫ SingleGlobalSource.map J M g K a U =
      homologyMap ((OrderedCech.TotalProjection.ordered U).map a) (g+g) ≫
        inv (Ordered.SingleGlobalSource.edgeMap g K U) := by
  simp only [SingleGlobalSource.map, Iso.hom_inv_id_assoc]

variable [IsIso (Ordered.SingleGlobalSource.edgeMap g K V)]
  (T : ν → Opens X)
  (rU : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι U)
  (rV : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk κ V)
  [IsIso (Ordered.SingleGlobalSource.edgeMap g K T)]
  [IsIso (homologyMap (OrderedCech.Refinement.map V T rV (J.obj M)) g)]

theorem common_refinement : SingleGlobalSource.map J M g K a U =
    Ordered.SingleGlobalSource.coefficientComparison (J.obj M) g U V T rU rV ≫
      SingleGlobalSource.map J M g K a V := by
  rw [map_eq, map_eq]
  exact Ordered.SingleGlobalSource.common_refinement (J.obj M) g K (plainMap J M g K a)
    U V T rU rV

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleGlobalSource
