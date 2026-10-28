import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Refinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalProjection

/-! # Complex Coefficient Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexCoefficientIso

noncomputable section

/-! Refinement invertibility is unchanged by an isomorphism of the
actual coefficient complexes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem square {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : D ⟶ E) (e : A ≅ D) (f : B ≅ E)
    [IsIso a] (h : a ≫ f.hom = e.hom ≫ b) : IsIso b := by
  have hb : b = e.inv ≫ a ≫ f.hom := by rw [h, Iso.inv_hom_id_assoc]
  rw [hb]
  infer_instance

universe u v
variable {X : TopCat.{u}} {D : Type v} [Category D] [Abelian D]
  [HasProducts.{u} D] [HasCoproducts.{0} D]
  {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ} (e : K ≅ L)
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : Opens X) (V : ι → Opens X) (W : κ → Opens X)
  (r : FormalCoproduct.mk κ W ⟶ FormalCoproduct.mk ι V) (q : ℕ)

def relativeIso := homologyMapIso
  (HomologicalComplex₂.total.mapIso
    (((RelativeCech.Total.localFunctor U V).mapHomologicalComplex (.up ℕ)).mapIso e)
    (.up ℕ)) q

def orderedIso := homologyMapIso ((OrderedCech.TotalProjection.ordered V).mapIso e) q

include e in
theorem relative [IsIso (RelativeCech.Refinement.homology U V W r K q)] :
    IsIso (RelativeCech.Refinement.homology U V W r L q) :=
  square _ _ (relativeIso e U V q) (relativeIso e U W q)
    (RelativeCech.Refinement.homology_naturality U V W r e.hom q).symm

include e in
theorem ordered [IsIso (homologyMap (OrderedCech.Refinement.totalMap V W r K) q)] :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap V W r L) q) :=
  square _ _ (orderedIso e V q) (orderedIso e W q)
    (Presheaf.OrderedCover.Comparison.homology_naturality V W r e.hom q).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexCoefficientIso
