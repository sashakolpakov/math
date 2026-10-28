import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.TotalResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.PowerVanishing

/-! # Total Top -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.TotalTop

noncomputable section

/-! In the actual top degree the mixed fraction map has only its
normal-top/full-intersection component. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C)
  (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

theorem component_zero (n p q : ℕ) (h : p + q = n) (hz : c < p ∨ m < q) :
    Components.component (c := c) R P U t ht n p q h = 0 := by
  apply Pi.hom_ext
  intro a
  have he := Components.component_projection R P U (0 : Fin c → R) t ht n p q h a
  refine he.trans ?_
  rw [zero_comp]
  rcases hz with hp | hq
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    have hx := Exterior.PowerVanishing.eq_zero (Pi.basisFun R (Fin c)) hp x
    change Components.coordinateAt R P U t ht n p q h a φ x = 0
    rw [hx, map_zero]
  · have hc := Fintype.card_le_of_injective a.val a.property.injective
    simp only [Fintype.card_fin, Fintype.card_ulift] at hc
    omega

theorem top_projection (p q : ℕ) (h : p + q = c + m) :
    (Total.map R P U s t ht).f (c + m) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (target R P U s)) p q (c + m) =
      (Components.component R P U t ht (c + m) c m rfl ≫
        (Components.target R P U s).ιTotal (.up ℕ) c m (c + m) rfl) ≫
          (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (target R P U s)) p q (c + m) := by
  rw [Total.map_projection R P U s t ht (c + m) p q h]
  by_cases hp : p = c
  · subst p
    have hq : q = m := by omega
    subst q
    simp
    exact (Category.comp_id _).symm
  · have hz : c < p ∨ m < q := by omega
    rw [component_zero R P U t ht (c + m) p q h hz, Category.assoc]
    simp [Ne.symm hp]

theorem top_map : (Total.map R P U s t ht).f (c + m) =
    Components.component R P U t ht (c + m) c m rfl ≫ (Components.target R P U s).ιTotal (.up ℕ) c m (c + m) rfl := by
  apply AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatCoordinates.Projective.totalUpNat_hom_ext (Components.target R P U s) (c + m)
  intro i
  exact top_projection R P U s t ht i (c + m - i) (by omega)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.TotalTop
