import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentLocalization

/-! # Quasicoherent Section Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentSectionExtension

noncomputable section

/-! Actual sections of a quasicoherent module over an affine scheme admit denominator clearing and power annihilation on intrinsic principal opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]

theorem affine_quasicoherent_section_clear_denominator
    (f : Γ(X, ⊤)) (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, ⊤)),
      M.presheaf.map (X.basicOpen f).leTop.op t =
        X.presheaf.map (X.basicOpen f).leTop.op (f ^ n) • s := by
  have h := QuasicoherentLocalization.affine_quasicoherent_sections_localize M f
  obtain ⟨n, t, ht⟩ := h.surj _ _ s
  exact ⟨n, t, ht.symm⟩

theorem affine_quasicoherent_section_vanishing
    (f : Γ(X, ⊤)) (t : Γ(M, ⊤))
    (ht : M.presheaf.map (X.basicOpen f).leTop.op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  let a := ((Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) M).map
    (X.basicOpen f).leTop.op).hom
  have : IsLocalizedModule.Away f a := QuasicoherentLocalization.affine_quasicoherent_sections_localize M f
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f) a).mp ht
  refine ⟨n, ?_⟩
  change X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_rfl)).op (f ^ n) • t = 0 at hn
  simpa using hn

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentSectionExtension
