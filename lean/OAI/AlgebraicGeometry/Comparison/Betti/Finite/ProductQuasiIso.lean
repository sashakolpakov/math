import OAI.AlgebraicGeometry.Comparison.Betti.Cech.FunctorAdditive
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Product Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.ProductQuasiIso.Total

noncomputable section

/-! Finite products preserve quasi-isomorphisms of actual cochain complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

theorem functor_piMap_comparison {C D : Type*} [Category* C] [Category* D]
    {ι : Type} (F : C ⥤ D) {K L : ι → C} [HasProduct K] [HasProduct L]
    [HasProduct (fun i => F.obj (K i))] [HasProduct (fun i => F.obj (L i))]
    (φ : ∀ i, K i ⟶ L i) :
    F.map (CategoryTheory.Limits.Pi.map φ) ≫ piComparison F L =
      piComparison F K ≫ CategoryTheory.Limits.Pi.map (fun i => F.map (φ i)) := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro i
  rw [Category.assoc, piComparison_comp_π, ← F.map_comp, CategoryTheory.Limits.Pi.map_π,
    F.map_comp, Category.assoc, CategoryTheory.Limits.Pi.map_π, ← Category.assoc, piComparison_comp_π]

theorem finiteProduct_quasiIso {C : Type*} [Category* C] [Abelian C]
    {ι : Type} [Finite ι] [HasProductsOfShape ι C]
    {K L : ι → CochainComplex C ℕ} (φ : ∀ i, K i ⟶ L i) (hφ : ∀ i, QuasiIso (φ i)) :
    QuasiIso (CategoryTheory.Limits.Pi.map φ) := by
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := homologyFunctor C (.up ℕ) n
  have hIso : IsIso (CategoryTheory.Limits.Pi.map (fun i => H.map (φ i))) := by
    have hi (i : ι) : QuasiIso (φ i) := hφ i
    exact (CategoryTheory.Limits.Pi.mapIso (fun i => isoOfQuasiIsoAt (φ i) n)).isIso_hom
  have hc : IsIso (H.map (CategoryTheory.Limits.Pi.map φ) ≫ piComparison H L) := by
    rw [functor_piMap_comparison H φ]
    infer_instance
  exact IsIso.of_isIso_comp_right (H.map (CategoryTheory.Limits.Pi.map φ)) (piComparison H L)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.ProductQuasiIso.Total
