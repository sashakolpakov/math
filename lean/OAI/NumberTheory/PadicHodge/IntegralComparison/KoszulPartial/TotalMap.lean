import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComponentSquares

/-! # Total Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.TotalMap

noncomputable section

/-! The actual mixed Koszul partial-fraction map to the supported
ordered Čech total, with the ordinary total differential sign. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Differential
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.CechDifferential
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C)
  (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

abbrev delta (n : ℕ) := ModuleCat.ofHom
  (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R (Fractions.ambient R (c := c) (m := m)) (Differential.equation R s t) n).dualMap
abbrev hp (p : ℕ) := Koszul.HomPresheaf.homPresheaf R (Fractions.normal R (c := c)) (Fractions.modules R P) p
abbrev hd (p : ℕ) := Koszul.HomPresheaf.differential R (Fractions.normal R (c := c)) (Fractions.modules R P)
  (Koszul.GeneratorMatrix.equation R s) p

theorem left (n : ℕ) :
    Components.component R P U t ht n 0 n (by omega) ≫ ((Components.target R P U s).X 0).d n (n + 1) =
      (Components.source R s t).d n (n + 1) ≫ Components.component R P U t ht (n + 1) 0 (n + 1) (by omega) := by
  rw [Components.vertical_d, ModuleCat.hom_ext_iff.mpr (Components.source_d R s t n)]
  apply Cech.ComponentSquares.vertical U (delta R s t n) (hp R P 0) n
    (fun a => ModuleCat.ofHom (Components.coordinateAt R P U t ht n 0 n (by omega) a))
    (fun a => ModuleCat.ofHom (Components.coordinateAt R P U t ht (n + 1) 0 (n + 1) (by omega) a))
  intro a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  change (∑ k : Fin (n + 1), (-1 : ℤ) ^ k.val •
    (P.map ((AugmentedOrdered.Cech.face U n k).φ a).op).hom.toLinearMap.comp
      (Components.coordinateAt R P U t ht n 0 n (by omega) (a.delete k) φ)) x = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  change (∑ k : Fin (n + 1), (-1 : ℤ) ^ k.val •
    (P.map ((AugmentedOrdered.Cech.face U n k).φ a).op).hom
      (CechDifferential.value R P U t ht 0 n n (by omega) (a.delete k) φ x)) =
    CechDifferential.value R P U t ht 0 (n + 1) (n + 1) (by omega) a
      (φ.comp (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Differential.equation R s t) n)) x
  simpa only [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one] using
    (Edges.left R s t P U ht n a φ x).symm

theorem right (n : ℕ) :
    Components.component R P U t ht n n 0 (by omega) ≫ ((Components.target R P U s).d n (n + 1)).f 0 =
      (Components.source R s t).d n (n + 1) ≫ Components.component R P U t ht (n + 1) (n + 1) 0 (by omega) := by
  rw [Components.horizontal_d, ModuleCat.hom_ext_iff.mpr (Components.source_d R s t n)]
  apply Cech.ComponentSquares.horizontal U (delta R s t n) (hd R P s n) 0
    (fun a => ModuleCat.ofHom (Components.coordinateAt R P U t ht n n 0 (by omega) a))
    (fun a => ModuleCat.ofHom (Components.coordinateAt R P U t ht (n + 1) (n + 1) 0 (by omega) a))
  intro a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  exact (Edges.right R s t P U ht n a φ x).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.TotalMap
