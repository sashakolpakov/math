import OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticNorm

/-! # Norm Kernel Open -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.NormKernelOpen.Construction

noncomputable section

/-! The given quadratic character has open kernel. This identifies the norm
subgroup as an open subgroup without invoking local class field theory. -/

theorem square_one_character_kernel_open
    {G : Type} [Group G] [TopologicalSpace G]
    (ω : G →ₜ* Circle) (hsq : ∀ g, ω g ^ 2 = 1) :
    IsOpen (ω.toMonoidHom.ker : Set G) := by
  have hc : Continuous (fun g : G => ‖(ω g : ℂ) - 1‖) :=
    ((continuous_subtype_val.comp ω.continuous).sub continuous_const).norm
  convert isOpen_lt hc (continuous_const : Continuous (fun _ : G => (1 : ℝ))) using 1
  ext g
  change ω g = 1 ↔ ‖(ω g : ℂ) - 1‖ < 1
  constructor
  · intro hg
    simp [hg]
  · intro hg
    have hz : (ω g : ℂ) ^ 2 = 1 := congrArg (fun z : Circle => (z : ℂ)) (hsq g)
    rcases sq_eq_one_iff.mp hz with h | h
    · exact Circle.ext h
    · rw [h] at hg
      norm_num at hg

theorem quadraticCharacter_kernel_open
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E] [FiniteDimensional F E]
    (hQuadratic : Module.finrank F E = 2) (ω : Fˣ →ₜ* Circle)
    (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω) :
    IsOpen (ω.toMonoidHom.ker : Set Fˣ) :=
  square_one_character_kernel_open ω (Characters.Construction.quadraticCharacter_square hQuadratic ω hω)

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.NormKernelOpen.Construction
