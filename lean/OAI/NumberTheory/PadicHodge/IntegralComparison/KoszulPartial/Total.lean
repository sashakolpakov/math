import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.TotalMap

/-! # Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Total

noncomputable section

/-! The literal mixed Koszul fraction morphism, including all total
degrees and the complete signed chain-map equation. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Differential
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.CechDifferential OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.TotalMap
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C)
  (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

theorem interior (p q : ℕ) :
    Components.component R P U t ht (p + q + 1) p (q + 1) (by omega) ≫
        ((Components.target R P U s).d p (p + 1)).f (q + 1) +
      ((-1 : ℤˣ) ^ (p + 1)) •
        (Components.component R P U t ht (p + q + 1) (p + 1) q (by omega) ≫
          ((Components.target R P U s).X (p + 1)).d q (q + 1)) =
    (Components.source R s t).d (p + q + 1) (p + q + 1 + 1) ≫
      Components.component R P U t ht (p + q + 1 + 1) (p + 1) (q + 1) (by omega) := by
  rw [Components.horizontal_d, Components.vertical_d, ModuleCat.hom_ext_iff.mpr (Components.source_d R s t (p + q + 1))]
  simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  apply Cech.ComponentSquares.mixed U (TotalMap.delta R s t (p + q + 1)) (TotalMap.hd R P s p) q
    ((-1 : ℤ) ^ (p + 1))
    (fun a => ModuleCat.ofHom (Components.coordinateAt R P U t ht (p + q + 1) p (q + 1) (by omega) a))
    (fun a => ModuleCat.ofHom (Components.coordinateAt R P U t ht (p + q + 1) (p + 1) q (by omega) a))
    (fun a => ModuleCat.ofHom (Components.coordinateAt R P U t ht (p + q + 1 + 1) (p + 1) (q + 1) (by omega) a))
  intro a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_add, ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply]
  change (Components.coordinateAt R P U t ht (p + q + 1) p (q + 1) (by omega) a φ)
      (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Koszul.GeneratorMatrix.equation R s) p x) +
    ((-1 : ℤ) ^ (p + 1) • (∑ k : Fin (q + 1), (-1 : ℤ) ^ k.val •
      (P.map ((AugmentedOrdered.Cech.face U q k).φ a).op).hom.toLinearMap.comp
        (Components.coordinateAt R P U t ht (p + q + 1) (p + 1) q (by omega) (a.delete k) φ))) x = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  change CechDifferential.value R P U t ht p (q + 1) (p + q + 1) rfl a φ
      (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Koszul.GeneratorMatrix.equation R s) p x) +
    (-1 : ℤ) ^ (p + 1) • (∑ k : Fin (q + 1), (-1 : ℤ) ^ k.val •
      (P.map ((AugmentedOrdered.Cech.face U q k).φ a).op).hom
        (CechDifferential.value R P U t ht (p + 1) q (p + q + 1) (by omega) (a.delete k) φ x)) =
    CechDifferential.value R P U t ht (p + 1) (q + 1) (p + q + 2) (by omega) a
      (φ.comp (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Differential.equation R s t) (p + q + 1))) x
  simpa only [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one] using
    (CechDifferential.differential R P U t ht s p q a φ x).symm

def data : TotalComponentMap.Data (Components.source R s t) (Components.target R P U s) where
  component := Components.component R P U t ht
  left := TotalMap.left R P U s t ht
  right := TotalMap.right R P U s t ht
  interior := Total.interior R P U s t ht

def map : Components.source R s t ⟶ (Components.target R P U s).total (.up ℕ) :=
  TotalComponentMap.map _ _ (data R P U s t ht)

@[reassoc]
theorem map_projection (n p q : ℕ) (h : p + q = n) :
    (Total.map R P U s t ht).f n ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (target R P U s)) p q n =
      Components.component R P U t ht n p q h :=
  TotalComponentMap.map_projection _ _ (data R P U s t ht) n p q h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Total
