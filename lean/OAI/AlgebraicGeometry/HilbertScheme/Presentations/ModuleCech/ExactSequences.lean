import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Maps

/-! # Exact Sequences -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.ExactSequences.ProjectiveCech

noncomputable section

/-! Homogeneous Čech cochains lift through graded surjections and exact sequences. -/

open _root_.MvPolynomial DirectSum

universe u v w t

variable {σ : Type u}
variable (R : Type v) [CommRing R]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable {N : Type t} [AddCommGroup N] [Module R N] [Module (MvPolynomial σ R) N]
  [IsScalarTower R (MvPolynomial σ R) N]
variable (ℳ : ℤ → Submodule R M) (𝒩 : ℤ → Submodule R N)

theorem moduleCechMap_lift_of_pointwise (f : M →ₗ[MvPolynomial σ R] N) (d : ℤ) (q : ℕ)
    (y : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R N) (hycard : Card.ProjectiveCech.ModuleCechCardSupported R N q y)
    (hlift : ∀ s, ∃ x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s,
      x ∈ Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d ∧ Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) f x = y s) :
    ∃ x : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
      Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d x ∧ Card.ProjectiveCech.ModuleCechCardSupported R M q x ∧ Maps.ProjectiveCech.moduleCechMap R f x = y := by
  choose x hx he using hlift
  let x' : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M := fun s => if s.card = q then x s else 0
  refine ⟨x', ?_, ?_, ?_⟩
  · intro s
    change (if s.card = q then x s else 0) ∈ Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d
    split_ifs
    · exact hx s
    · exact Submodule.zero_mem _
  · intro s hs
    exact ite_eq_right hs
  · funext s
    change Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) f (if s.card = q then x s else 0) = y s
    split_ifs with hs
    · exact he s
    · rw [map_zero, hycard s hs]

variable [Decomposition ℳ] [Decomposition 𝒩]
variable [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) 𝒩]

theorem moduleCechMap_lift (f : M →ₗ[MvPolynomial σ R] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (hs : Function.Surjective f) (d : ℤ) (q : ℕ)
    (y : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R N) (hy : Card.ProjectiveCech.ModuleCechHomogeneous R N 𝒩 d y)
    (hycard : Card.ProjectiveCech.ModuleCechCardSupported R N q y) :
    ∃ x : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
      Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d x ∧ Card.ProjectiveCech.ModuleCechCardSupported R M q x ∧ Maps.ProjectiveCech.moduleCechMap R f x = y := by
  apply moduleCechMap_lift_of_pointwise R ℳ f d q y hycard
  intro s
  obtain ⟨x, hx⟩ := Localized.GradedExactness.GradedModules.localizedDegreeMap_surjective (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ 𝒩
    (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) f hf hs d ⟨y s, hy s⟩
  exact ⟨x.val, x.property, congrArg Subtype.val hx⟩

variable {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial σ R) P]
  [IsScalarTower R (MvPolynomial σ R) P]
variable (ℙ : ℤ → Submodule R P)

theorem moduleCechMap_kernel_lift (f : M →ₗ[MvPolynomial σ R] N) (g : N →ₗ[MvPolynomial σ R] P)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (hg : ∀ d n, n ∈ 𝒩 d → g n ∈ ℙ d)
    (hex : Function.Exact f g) (d : ℤ) (q : ℕ)
    (y : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R N) (hy : Card.ProjectiveCech.ModuleCechHomogeneous R N 𝒩 d y)
    (hycard : Card.ProjectiveCech.ModuleCechCardSupported R N q y) (hyzero : Maps.ProjectiveCech.moduleCechMap R g y = 0) :
    ∃ x : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
      Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d x ∧ Card.ProjectiveCech.ModuleCechCardSupported R M q x ∧ Maps.ProjectiveCech.moduleCechMap R f x = y := by
  apply moduleCechMap_lift_of_pointwise R ℳ f d q y hycard
  intro s
  have he := Localized.GradedExactness.GradedModules.localizedDegreeMap_exact (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ 𝒩 ℙ
    (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) f g hf hg hex d
  have hz : Localized.GradedExactness.GradedModules.localizedDegreeMap (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) 𝒩 ℙ (LaurentMonomials.ProjectiveCech.inversionMonomial R s)
      (s.card : ℤ) (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) g hg d ⟨y s, hy s⟩ = 0 :=
    Subtype.ext (congrFun hyzero s)
  obtain ⟨x, hx⟩ := (he ⟨y s, hy s⟩).mp hz
  exact ⟨x.val, x.property, congrArg Subtype.val hx⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.ExactSequences.ProjectiveCech
