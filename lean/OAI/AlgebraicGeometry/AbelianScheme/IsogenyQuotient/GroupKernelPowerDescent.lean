import OAI.AlgebraicGeometry.FormalGeometry.Completion.OverEffectiveDescent
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupDescent

/-! # Group Kernel Power Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupKernelPowerDescent.Construction

noncomputable section

/-! A multiplication map descends through a faithfully flat group
quotient when its actual kernel is killed by that multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
  (q : A ⟶ B) [IsMonHom q] [EffectiveEpi q.left]
  [Epi (q ⊗ₘ q)]

theorem groupHom_descends_of_kernel (f : A ⟶ C) [IsMonHom f]
    (hf : ∀ (T : Over S) (x : T ⟶ A), x ≫ q = 1 → x ≫ f = 1) :
    ∃ g : B ⟶ C, IsMonHom g ∧ q ≫ g = f := by
  obtain ⟨g, hg, _⟩ := FormalGeometry.Completion.OverEffectiveDescent.Construction.over_existsUnique_desc_of_effectiveEpi q f (by
    intro T a b hab
    have hkill := hf T (a / b) (by rw [GrpObj.div_comp, hab, div_self'])
    rw [GrpObj.div_comp] at hkill
    exact div_eq_one.mp hkill)
  have : IsMonHom g := {
    one_hom := by
      rw [← IsMonHom.one_hom q, Category.assoc, hg, IsMonHom.one_hom f]
    mul_hom := by
      apply (cancel_epi (q ⊗ₘ q)).mp
      rw [← Category.assoc, ← IsMonHom.mul_hom q, Category.assoc, hg,
        IsMonHom.mul_hom f, ← Category.assoc, tensorHom_comp_tensorHom, hg]
  }
  exact ⟨g, inferInstance, hg⟩

omit [GrpObj C] in
theorem exists_groupKernel_power_complement [IsCommMonObj A] (n : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ A), x ≫ q = 1 → x ^ n = 1) :
    ∃ v : B ⟶ A, IsMonHom v ∧ q ≫ v = (𝟙 A) ^ n := by
  have : IsMonHom ((𝟙 A) ^ n) := Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom _ _
  apply groupHom_descends_of_kernel q ((𝟙 A) ^ n)
  intro T x hx
  simpa only [MonObj.comp_pow, Category.comp_id] using hn T x hx

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupKernelPowerDescent.Construction
