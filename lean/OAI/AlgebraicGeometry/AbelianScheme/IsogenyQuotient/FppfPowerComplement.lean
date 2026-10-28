import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupKernelPowerDescent

/-! # Fppf Power Complement -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FppfPowerComplement.Construction

noncomputable section

/-! The actual multiplication map descends through an fpqc group
quotient, with both complementary composition identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A]
  (f : A ⟶ B) [IsMonHom f] [Flat f.left] [Surjective f.left] [QuasiCompact f.left]

theorem exists_fppf_power_complement (n : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1) :
    ∃ r : B ⟶ A, IsMonHom r ∧ f ≫ r = (𝟙 A) ^ n ∧ r ≫ f = (𝟙 B) ^ n := by
  have : EffectiveEpi f := Picard.Homomorphisms.GroupDescent.Construction.effectiveEpi_over_of_fpqc f
  have : EffectiveEpi (f ⊗ₘ f) := Picard.Homomorphisms.GroupDescent.Construction.effectiveEpi_tensor_over_of_fpqc f f
  obtain ⟨r, hrmon, hfr⟩ := GroupKernelPowerDescent.Construction.exists_groupKernel_power_complement f n hn
  refine ⟨r, hrmon, hfr, ?_⟩
  apply (cancel_epi f).mp
  rw [← Category.assoc, hfr, MonObj.pow_comp, Category.id_comp, MonObj.comp_pow, Category.comp_id]

omit [Flat f.left] [Surjective f.left] [QuasiCompact f.left] in
theorem powerComplement_kernel_torsion (r : B ⟶ A) (n : ℕ) (hrf : r ≫ f = (𝟙 B) ^ n)
    (T : Over S) (x : T ⟶ B) (hx : x ≫ r = 1) : x ^ n = 1 := by
  have h := congrArg (fun a => x ≫ a) hrf
  rw [← Category.assoc, hx, MonObj.one_comp, MonObj.comp_pow, Category.comp_id] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FppfPowerComplement.Construction
