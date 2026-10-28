import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomAcyclic

/-! # Hom Acyclic Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomAcyclicProducts

noncomputable section

/-! Exact coefficient Hom rows are preserved by actual products and
retracts. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K : CochainComplex C ℕ}

theorem rows_retract {M N : C} (hM : HomAcyclic.Rows K M) (i : N ⟶ M) (p : M ⟶ N) (hip : i ≫ p = 𝟙 N) :
    HomAcyclic.Rows K N := by
  constructor
  · intro f
    obtain ⟨g, hg⟩ := hM.zero (f ≫ i)
    exact ⟨g ≫ p, by rw [← Category.assoc, hg, Category.assoc, hip, Category.comp_id]⟩
  · intro n f hf
    obtain ⟨g, hg⟩ := hM.succ n (f ≫ i) (by rw [← Category.assoc, hf, zero_comp])
    exact ⟨g ≫ p, by rw [← Category.assoc, hg, Category.assoc, hip, Category.comp_id]⟩

theorem rows_pi {ι : Type w} (M : ι → C) [HasProduct M] (hM : ∀ i, HomAcyclic.Rows K (M i)) :
    HomAcyclic.Rows K (∏ᶜ M) := by
  constructor
  · intro f
    choose g hg using fun i => (hM i).zero (f ≫ Pi.π M i)
    refine ⟨Pi.lift g, ?_⟩
    apply Pi.hom_ext
    intro i
    rw [Category.assoc, Pi.lift_comp_π, hg]
  · intro n f hf
    choose g hg using fun i => (hM i).succ n (f ≫ Pi.π M i)
      (by rw [← Category.assoc, hf, zero_comp])
    refine ⟨Pi.lift g, ?_⟩
    apply Pi.hom_ext
    intro i
    rw [Category.assoc, Pi.lift_comp_π, hg]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomAcyclicProducts
