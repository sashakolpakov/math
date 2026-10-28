import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CommonRefinementNaturality

/-! # Presheaf Common Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PresheafCommonRefinement

noncomputable section

/-! The literal relative common-refinement map with the coefficient
universe independent of the topological space. This permits the native
large coefficient category without changing the original map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X : TopCat.{u}} (U : Opens X)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (V : ι → Opens X) (W : κ → Opens X) (T : ν → Opens X)
  (r : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι V)
  (s : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk κ W)
  {D : Type v} [Category D] [Abelian D] [HasProducts.{u} D] [HasCoproducts.{0} D]

def comparison (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) (q : ℕ)
    [IsIso (RelativeCech.Refinement.homology U W T s K q)] :=
  RelativeCech.Refinement.homology U V T r K q ≫
    inv (RelativeCech.Refinement.homology U W T s K q) ≫
      homologyMap (RelativeCech.Total.map U W K) q

theorem naturality {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ}
    (a : K ⟶ L) (q : ℕ)
    [IsIso (RelativeCech.Refinement.homology U W T s K q)]
    [IsIso (RelativeCech.Refinement.homology U W T s L q)] :
    homologyMap (RelativeCech.Total.sourceMap U V a) q ≫ comparison U V W T r s L q =
      comparison U V W T r s K q ≫ homologyMap (RelativeCech.Total.targetMap U W a) q := by
  have hi : homologyMap (RelativeCech.Total.sourceMap U T a) q ≫
      inv (RelativeCech.Refinement.homology U W T s L q) =
    inv (RelativeCech.Refinement.homology U W T s K q) ≫
      homologyMap (RelativeCech.Total.sourceMap U W a) q := by
    simpa only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id,
      Category.comp_id] using
      congrArg (fun z => inv (RelativeCech.Refinement.homology U W T s K q) ≫ z ≫
        inv (RelativeCech.Refinement.homology U W T s L q))
        (RelativeCech.Refinement.homology_naturality U W T s a q).symm
  dsimp only [comparison]
  rw [← Category.assoc, RelativeCech.Refinement.homology_naturality U V T r a q]
  simp only [Category.assoc]
  rw [← Category.assoc (homologyMap (RelativeCech.Total.sourceMap U T a) q), hi]
  simp only [Category.assoc]
  rw [RelativeCech.Total.homology_naturality U W a q]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PresheafCommonRefinement
