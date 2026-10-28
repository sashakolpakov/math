import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalOf

/-! # Local Differential Normal Form -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalDifferentialNormalForm.Construction.LocalSectionLifting

noncomputable section

/-! Existence of a minimal form for a map of finite free modules over a local ring. -/

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem exists_localMinimalDifferential_of_finrank (n : ℕ) :
    ∀ (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Free R M]
      [Module.Finite R N] [Module.Free R N],
      Module.finrank R M = n → ∀ f : M →ₗ[R] N, Nonempty (LocalMinimalOf.Construction.LocalSectionLifting.LocalMinimalDifferential f) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro M N hMF hMFree hNF hNFree hn f
    by_cases hf : f.baseChange (IsLocalRing.ResidueField R) = 0
    · exact ⟨LocalMinimalOf.Construction.LocalSectionLifting.localMinimalDifferentialOfResidueZero f hf⟩
    obtain ⟨i, j, eM, eN, g, d, hd⟩ := LocalGaussianStep.Construction.LocalSectionLifting.exists_gaussian_step_of_residue_ne_zero
      (Module.finBasis R M) (Module.finBasis R N) f hf
    let M₁ : ModuleCat.{u} R := ModuleCat.of R ({l : Fin (Module.finrank R M) // l ≠ i} → R)
    let N₁ : ModuleCat.{u} R := ModuleCat.of R ({l : Fin (Module.finrank R N) // l ≠ j} → R)
    have hlt : Module.finrank R M₁ < n := by
      change Module.finrank R ({l : Fin (Module.finrank R M) // l ≠ i} → R) < n
      rw [Module.finrank_fintype_fun_eq_card]
      have hc := Fintype.card_subtype_lt (p := fun l : Fin (Module.finrank R M) => l ≠ i)
        (x := i) (not_not.mpr rfl)
      simpa only [Fintype.card_fin, hn] using hc
    obtain ⟨P⟩ := ih (Module.finrank R M₁) hlt M₁ N₁ rfl g
    exact ⟨LocalMinimalOf.Construction.LocalSectionLifting.localMinimalDifferentialStep (M₁ := M₁) (N₁ := N₁) f g eM eN d hd P⟩

theorem exists_localMinimalDifferential (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Free R M] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] N) : Nonempty (LocalMinimalOf.Construction.LocalSectionLifting.LocalMinimalDifferential f) :=
  exists_localMinimalDifferential_of_finrank (Module.finrank R M) M N rfl f

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalDifferentialNormalForm.Construction.LocalSectionLifting
