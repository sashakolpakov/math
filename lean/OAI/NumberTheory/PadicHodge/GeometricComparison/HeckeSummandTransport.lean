import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

/-! # Hecke Summand Transport -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeSummandTransport.GeneralizedHecke

noncomputable section

/-! Actual intertwining equivalences transport simultaneous generalized eigenspaces, without semisimplicity or a finite Hecke index set. -/

variable {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem intertwines_power (e : V ≃ₗ[K] W) (T : Module.End K V) (U : Module.End K W)
    (h : ∀ x, e (T x) = U (e x)) (n : ℕ) (x : V) : e ((T ^ n) x) = (U ^ n) (e x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]

theorem mem_maxGenEigenspace_equiv (e : V ≃ₗ[K] W) (T : Module.End K V) (U : Module.End K W)
    (h : ∀ x, e (T x) = U (e x)) (μ : K) (x : V) :
    e x ∈ U.maxGenEigenspace μ ↔ x ∈ T.maxGenEigenspace μ := by
  have hshift : ∀ x, e ((T - μ • 1) x) = (U - μ • 1) (e x) := by
    intro y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, h]
  simp only [Module.End.mem_maxGenEigenspace]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, e.injective ?_⟩
    exact (intertwines_power e _ _ hshift n x).trans (hn.trans e.map_zero.symm)
  · rintro ⟨n, hn⟩
    exact ⟨n, (intertwines_power e _ _ hshift n x).symm.trans ((congrArg e hn).trans e.map_zero)⟩

theorem summand_map (e : V ≃ₗ[K] W) (T : I → Module.End K V) (U : I → Module.End K W)
    (h : ∀ i x, e (T i x) = U i (e x)) (χ : I → K) :
    (Linear.generalizedHeckeSummand T χ).map e.toLinearMap = Linear.generalizedHeckeSummand U χ := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Submodule.mem_map_equiv]
  simp only [e.symm_apply_apply, Linear.mem_generalizedHeckeSummand]
  exact forall_congr' (fun i => (mem_maxGenEigenspace_equiv e (T i) (U i) (h i) (χ i) x).symm)

theorem summand_ne_bot_iff (e : V ≃ₗ[K] W) (T : I → Module.End K V) (U : I → Module.End K W)
    (h : ∀ i x, e (T i x) = U i (e x)) (χ : I → K) :
    Linear.generalizedHeckeSummand T χ ≠ ⊥ ↔ Linear.generalizedHeckeSummand U χ ≠ ⊥ := by
  rw [← summand_map e T U h χ]
  have hb : (Linear.generalizedHeckeSummand T χ).map e.toLinearMap = ⊥ ↔
      Linear.generalizedHeckeSummand T χ = ⊥ := by
    constructor
    · intro hbot
      apply Submodule.map_injective_of_injective e.injective
      simpa only [Submodule.map_bot] using hbot
    · intro hbot
      rw [hbot, Submodule.map_bot]
  exact not_congr hb.symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeSummandTransport.GeneralizedHecke
