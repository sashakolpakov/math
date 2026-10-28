import OAI.NumberTheory.PadicHodge.IntegralComparison.CountableProductHomology

/-! # Countable Cohomology Difference -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CountableCohomologyDifference

noncomputable section

/-!
# IntegralComparison: the difference operator on product cohomology has the expected coordinates
-/

open _root_.CategoryTheory

universe u

theorem cancel_iso_projection {C : Type*} [Category* C] [Preadditive C]
    {X Y Z W : C} (e : X ≅ Y) (d : X ⟶ X) (a : Y ⟶ Z) (b : Y ⟶ W) (t : W ⟶ Z)
    (h : d ≫ e.hom ≫ a = e.hom ≫ a - (e.hom ≫ b) ≫ t) :
    (e.inv ≫ d ≫ e.hom) ≫ a = a - b ≫ t := by
  have h' := congrArg (fun f => e.inv ≫ f) h
  simpa only [Category.assoc, Preadditive.comp_sub, Iso.inv_hom_id_assoc] using h'

variable (R : Type u) [CommRing R] (K : CochainComplex (Discrete ℕ ⥤ ModuleCat.{u} R) ℕ)
  (φ : CountableProductHomology.complex R K ⟶ CountableProductHomology.complex R K)
  (t : ∀ n, CountableProductHomology.component R K (n + 1) ⟶ CountableProductHomology.component R K n)
  (hφ : ∀ n, φ ≫ CountableProductHomology.projection R K n =
    CountableProductHomology.projection R K n - CountableProductHomology.projection R K (n + 1) ≫ t n)

include hφ in
theorem homology_projection (i n : ℕ) :
    HomologicalComplex.homologyMap φ i ≫ (CountableProductHomology.homologyIso R K i).hom ≫
      ModuleCat.ofHom (LinearMap.proj n) =
        (CountableProductHomology.homologyIso R K i).hom ≫ ModuleCat.ofHom (LinearMap.proj n) -
          ((CountableProductHomology.homologyIso R K i).hom ≫ ModuleCat.ofHom (LinearMap.proj (n + 1))) ≫
            HomologicalComplex.homologyMap (t n) i := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) i
  have h := congrArg H.map (hφ n)
  rw [H.map_comp, H.map_sub, H.map_comp] at h
  exact (congrArg (fun a => HomologicalComplex.homologyMap φ i ≫ a)
    (CountableProductHomology.homologyIso_projection R K i n)).trans
      (h.trans (congrArg₂ (· - ·) (CountableProductHomology.homologyIso_projection R K i n).symm
        (congrArg (fun a => a ≫ HomologicalComplex.homologyMap (t n) i)
          (CountableProductHomology.homologyIso_projection R K i (n + 1)).symm)))

def difference (i : ℕ) : ModuleCat.of R (∀ n, (CountableProductHomology.component R K n).homology i) ⟶
    ModuleCat.of R (∀ n, (CountableProductHomology.component R K n).homology i) :=
  (CountableProductHomology.homologyIso R K i).inv ≫ HomologicalComplex.homologyMap φ i ≫
    (CountableProductHomology.homologyIso R K i).hom

include hφ in
theorem difference_projection (i n : ℕ) :
    difference R K φ i ≫ ModuleCat.ofHom (LinearMap.proj n) =
      ModuleCat.ofHom (LinearMap.proj n) - ModuleCat.ofHom (LinearMap.proj (n + 1)) ≫
        HomologicalComplex.homologyMap (t n) i := by
  exact cancel_iso_projection (CountableProductHomology.homologyIso R K i)
    (HomologicalComplex.homologyMap φ i) (ModuleCat.ofHom (LinearMap.proj n))
    (ModuleCat.ofHom (LinearMap.proj (n + 1))) (HomologicalComplex.homologyMap (t n) i)
    (homology_projection R K φ t hφ i n)

include hφ in
theorem difference_apply (i : ℕ) (x : ∀ n, (CountableProductHomology.component R K n).homology i) (n : ℕ) :
    difference R K φ i x n = x n - HomologicalComplex.homologyMap (t n) i (x (n + 1)) :=
  congrArg (fun a : ModuleCat.of R (∀ n, (CountableProductHomology.component R K n).homology i) ⟶
    (CountableProductHomology.component R K n).homology i => a x) (difference_projection R K φ t hφ i n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CountableCohomologyDifference
