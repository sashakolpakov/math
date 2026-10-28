import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleCoordinates
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Single Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleEvaluation

noncomputable section

/-! Evaluate the surviving component of a mapped single-complex map
through a specified factorization in a module diagram. -/
open _root_.CategoryTheory _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {J : Type u} [Category.{v} J] (A : Type u) [Ring A] (r : J)
  (K : CochainComplex (J ⥤ ModuleCat.{u} A) ℕ)
  (N : J ⥤ ModuleCat.{u} A) (n : ℕ)
  (a : K ⟶ (single (J ⥤ ModuleCat.{u} A) (.up ℕ) n).obj N)
private abbrev evaluate : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A :=
  (evaluation J (ModuleCat.{u} A)).obj r
variable {L : CochainComplex (ModuleCat.{u} A) ℕ}
  (b : L ⟶ ((evaluate A r).mapHomologicalComplex (.up ℕ)).obj K)
  {P : ModuleCat.{u} A} (e : N.obj r ⟶ P)
  {D E : J ⥤ ModuleCat.{u} A}
  (f : K.X n ⟶ D) (g : D ⟶ E) (h : E ⟶ N)
  (ha : a.f n ≫ (singleObjXSelf (.up ℕ) n N).hom = f ≫ g ≫ h)
  (x : L.X n)

include ha in
theorem map_apply :
    (singleObjXSelf (.up ℕ) n P).hom
      (((b ≫ SingleCoordinates.map (evaluate A r) K N n a ≫
        (single (ModuleCat.{u} A) (.up ℕ) n).map e).f n) x) =
      e (h.app r (g.app r (f.app r (b.f n x)))) := by
  have hc := SingleCoordinates.compose_top (evaluate A r) K N n a b e
  rw [ha] at hc
  have hm : (evaluate A r).map (f ≫ g ≫ h) = f.app r ≫ g.app r ≫ h.app r := rfl
  rw [hm] at hc
  have hx := ConcreteCategory.congr_hom hc x
  change _ = e (h.app r (g.app r (f.app r (b.f n x)))) at hx
  exact hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleEvaluation
