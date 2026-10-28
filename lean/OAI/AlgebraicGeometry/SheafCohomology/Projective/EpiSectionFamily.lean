import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Epi Section Family -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.EpiSectionFamily

noncomputable section

/-! Epimorphic families are preserved by coproduct-preserving functors and changes of frames. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem epi_sigmaDesc_map {C D : Type*} [Category* C] [Category* D]
    {ι : Type*} (F : C ⥤ D) (M : ι → C) {N : C} (s : ∀ i, M i ⟶ N)
    [HasCoproduct M] [HasCoproduct (fun i => F.obj (M i))]
    [PreservesColimit (Discrete.functor M) F] [Epi (F.map (Sigma.desc s))] :
    Epi (Sigma.desc (fun i => F.map (s i))) := by
  have h : Sigma.desc (fun i => F.map (s i)) = sigmaComparison F M ≫ F.map (Sigma.desc s) := by
    ext i
    simp
  rw [h]
  infer_instance

theorem epi_sigmaDesc_precomp_iso {C : Type*} [Category* C] {ι : Type*}
    (M N : ι → C) {P : C} (e : ∀ i, M i ≅ N i) (s : ∀ i, N i ⟶ P)
    [HasCoproductsOfShape ι C] [Epi (Sigma.desc s)] :
    Epi (Sigma.desc (fun i => (e i).hom ≫ s i)) := by
  have h : Sigma.desc (fun i => (e i).hom ≫ s i) =
      (Sigma.mapIso e).hom ≫ Sigma.desc s := by
    ext i
    simp
  rw [h]
  infer_instance

theorem epi_sigmaDesc_postcomp_iso {C : Type*} [Category* C] {ι : Type*}
    (M : ι → C) {N P : C} (s : ∀ i, M i ⟶ N) (e : N ≅ P)
    [HasCoproduct M] [Epi (Sigma.desc s)] :
    Epi (Sigma.desc (fun i => s i ≫ e.hom)) := by
  have h : Sigma.desc (fun i => s i ≫ e.hom) = Sigma.desc s ≫ e.hom := by
    ext i
    simp
  rw [h]
  infer_instance

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.EpiSectionFamily
