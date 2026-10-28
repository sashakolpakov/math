import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.DimensionShift

/-! # Exact Left -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ExactLeft.ProjectiveCech

noncomputable section

/-! Exactness at the left end of a short exact sequence of graded projective Čech complexes. -/

open _root_.MvPolynomial DirectSum

universe u v w t

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)

theorem moduleCechExactAt_zero_vanish (d : ℤ)
    (hex : DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d 0)
    (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) (hf : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f)
    (hcard : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M 0 f) (hcycle : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f = 0) : f = 0 := by
  obtain ⟨g, _, hgc, hgd⟩ := hex f hf hcard hcycle
  have hdc := ModuleCech.Card.ProjectiveCech.moduleCechDifferential_card R M 0 g hgc
  funext s
  by_cases hs : s.card = 0
  · exact (congrFun hgd s).symm.trans (hdc s (by omega))
  · exact hcard s hs

variable {N : Type t} [AddCommGroup N] [Module R N] [Module (MvPolynomial σ R) N]
  [IsScalarTower R (MvPolynomial σ R) N]
variable (𝒩 : ℤ → Submodule R N)

theorem moduleCechExactAt_zero_of_injective
    [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
    [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) 𝒩]
    (i : M →ₗ[MvPolynomial σ R] N)
    (hi : ∀ d m, m ∈ ℳ d → i m ∈ 𝒩 d) (hinj : Function.Injective i)
    (d : ℤ) (hN : DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R N 𝒩 d 0) :
    DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d 0 := by
  intro f hf hcard hcycle
  have hif : ModuleCech.Maps.ProjectiveCech.moduleCechMap R i f = 0 :=
    moduleCechExactAt_zero_vanish R N 𝒩 d hN _
      (ModuleCech.Maps.ProjectiveCech.moduleCechMap_homogeneous R ℳ 𝒩 i hi d f hf)
      (ModuleCech.Maps.ProjectiveCech.moduleCechMap_card R i 0 f hcard) (by rw [← ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, hcycle, map_zero])
  have hz : f = 0 := (ModuleCech.Maps.ProjectiveCech.moduleCechMap_injective R i hinj) (hif.trans (map_zero _).symm)
  refine ⟨0, fun _ => Submodule.zero_mem _, fun _ _ => rfl, ?_⟩
  rw [map_zero, hz]

variable {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial σ R) P]
  [IsScalarTower R (MvPolynomial σ R) P]
variable (ℙ : ℤ → Submodule R P)
variable [Decomposition ℳ] [Decomposition 𝒩] [Decomposition ℙ]
variable [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) 𝒩]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℙ]

theorem moduleCech_exact_left (i : M →ₗ[MvPolynomial σ R] N) (p : N →ₗ[MvPolynomial σ R] P)
    (hi : ∀ d m, m ∈ ℳ d → i m ∈ 𝒩 d) (hp : ∀ d n, n ∈ 𝒩 d → p n ∈ ℙ d)
    (hinj : Function.Injective i) (hsurj : Function.Surjective p) (hex : Function.Exact i p)
    (d : ℤ) (q : ℕ) (hN : DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R N 𝒩 d (q + 1))
    (hP : DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R P ℙ d q) :
    DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d (q + 1) := by
  intro f hf hcard hcycle
  have hif := ModuleCech.Maps.ProjectiveCech.moduleCechMap_homogeneous R ℳ 𝒩 i hi d f hf
  have hic := ModuleCech.Maps.ProjectiveCech.moduleCechMap_card R i (q + 1) f hcard
  have hid : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R N (ModuleCech.Maps.ProjectiveCech.moduleCechMap R i f) = 0 := by
    rw [← ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, hcycle, map_zero]
  obtain ⟨y, hy, hyc, hyd⟩ := hN (ModuleCech.Maps.ProjectiveCech.moduleCechMap R i f) hif hic hid
  simp only [Nat.add_sub_cancel] at hyc
  have hpy := ModuleCech.Maps.ProjectiveCech.moduleCechMap_homogeneous R 𝒩 ℙ p hp d y hy
  have hpc := ModuleCech.Maps.ProjectiveCech.moduleCechMap_card R p q y hyc
  have hpd : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R P (ModuleCech.Maps.ProjectiveCech.moduleCechMap R p y) = 0 := by
    rw [← ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, hyd]
    exact (ModuleCech.Maps.ProjectiveCech.moduleCechMap_exact R i p hex _).mpr ⟨f, rfl⟩
  have hcorrect : ∃ z : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R N,
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R N 𝒩 d z ∧ ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R N q z ∧
      ModuleCech.Maps.ProjectiveCech.moduleCechMap R p z = 0 ∧ ModuleCech.Card.ProjectiveCech.moduleCechDifferential R N z = ModuleCech.Maps.ProjectiveCech.moduleCechMap R i f := by
    cases q with
    | zero =>
      exact ⟨y, hy, hyc, moduleCechExactAt_zero_vanish R P ℙ d hP _ hpy hpc hpd, hyd⟩
    | succ q =>
      obtain ⟨a, ha, hac, had⟩ := hP _ hpy hpc hpd
      simp only [Nat.add_sub_cancel] at hac
      obtain ⟨b, hb, hbc, hbp⟩ := ModuleCech.ExactSequences.ProjectiveCech.moduleCechMap_lift R 𝒩 ℙ p hp hsurj d q a ha hac
      refine ⟨y - ModuleCech.Card.ProjectiveCech.moduleCechDifferential R N b, ?_, ?_, ?_, ?_⟩
      · intro s
        exact Submodule.sub_mem _ (hy s) (ModuleCech.Card.ProjectiveCech.moduleCechDifferential_homogeneous R N 𝒩 d b hb s)
      · intro s hs
        change y s - ModuleCech.Card.ProjectiveCech.moduleCechDifferential R N b s = 0
        rw [hyc s hs, ModuleCech.Card.ProjectiveCech.moduleCechDifferential_card R N q b hbc s hs, sub_self]
      · rw [map_sub, ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, hbp, had, sub_self]
      · rw [map_sub, ModuleCech.Square.ProjectiveCech.moduleCechDifferential_square, sub_zero, hyd]
  obtain ⟨z, hz, hzc, hzp, hzd⟩ := hcorrect
  obtain ⟨g, hg, hgc, hgi⟩ := ModuleCech.ExactSequences.ProjectiveCech.moduleCechMap_kernel_lift R ℳ 𝒩 ℙ i p hi hp hex d q z hz hzc hzp
  refine ⟨g, hg, hgc, ?_⟩
  apply ModuleCech.Maps.ProjectiveCech.moduleCechMap_injective R i hinj
  rw [ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, hgi, hzd]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ExactLeft.ProjectiveCech
