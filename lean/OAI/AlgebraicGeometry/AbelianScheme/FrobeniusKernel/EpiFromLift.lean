import Mathlib.CategoryTheory.Abelian.Basic

/-! # Epi From Lift -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EpiFromLift.Construction

noncomputable section

/-! A map surjects if its composite does and the remaining kernel is
covered by elements that lift through the map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

theorem epi_of_iso_commutative_square {C : Type u} [Category.{v} C]
    {A B X Y : C} (e : A ≅ X) (e' : B ≅ Y) (f : A ⟶ B) (g : X ⟶ Y)
    (hg : Epi g) (h : f ≫ e'.hom = e.hom ≫ g) : Epi f := by
  have hf : f = e.hom ≫ g ≫ e'.inv := by
    calc
      f = (f ≫ e'.hom) ≫ e'.inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = (e.hom ≫ g) ≫ e'.inv := congrArg (fun a => a ≫ e'.inv) h
      _ = e.hom ≫ g ≫ e'.inv := Category.assoc _ _ _
  rw [hf]
  exact epi_comp' inferInstance (epi_comp' hg inferInstance)

theorem epi_of_composite_epi_of_kernel_lift {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z W : C} (g : X ⟶ Y) (f : Y ⟶ Z) [Epi (g ≫ f)]
    (r : W ⟶ kernel f) [Epi r] (a : W ⟶ X)
    (ha : a ≫ g = r ≫ kernel.ι f) : Epi g := by
  have : Epi f := epi_of_epi g f
  have hk : kernel.ι f ≫ cokernel.π g = 0 := by
    apply (cancel_epi r).mp
    rw [comp_zero, ← Category.assoc, ← ha, Category.assoc, cokernel.condition, comp_zero]
  let d := Abelian.epiDesc f (cokernel.π g) hk
  have hd : f ≫ d = cokernel.π g := Abelian.comp_epiDesc f (cokernel.π g) hk
  have hz : d = 0 := by
    apply (cancel_epi (g ≫ f)).mp
    rw [comp_zero, Category.assoc, hd, cokernel.condition]
  apply Abelian.epi_of_cokernel_π_eq_zero
  exact hd.symm.trans (by rw [hz, comp_zero])

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EpiFromLift.Construction
