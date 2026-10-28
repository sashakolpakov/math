import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.DimensionShift

/-! # Degree Map Exactness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.DegreeMapExactness.ProjectiveCech

noncomputable section

/-! Degreewise chart isomorphisms preserve and reflect exactness of actual projective Čech cochains. -/

open _root_.MvPolynomial

universe u v w t

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable {N : Type t} [AddCommGroup N] [Module R N] [Module (MvPolynomial σ R) N]
  [IsScalarTower R (MvPolynomial σ R) N]
variable (ℳ : ℤ → Submodule R M) (𝒩 : ℤ → Submodule R N)
variable [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) 𝒩]
variable (f : M →ₗ[MvPolynomial σ R] N) (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d)

def moduleCechDegreeMap (d : ℤ) (s : Finset σ) :
    Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d →ₗ[R] Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R N 𝒩 s d :=
  Localized.GradedExactness.GradedModules.localizedDegreeMap (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ 𝒩 (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ)
    (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) f hf d

omit [LinearOrder σ] [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) 𝒩] in
theorem moduleCechMap_homogeneous_injective (d : ℤ)
    (hinj : ∀ s : Finset σ, Function.Injective (moduleCechDegreeMap R ℳ 𝒩 f hf d s))
    (x y : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
    (hx : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d x) (hy : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d y)
    (hxy : ModuleCech.Maps.ProjectiveCech.moduleCechMap R f x = ModuleCech.Maps.ProjectiveCech.moduleCechMap R f y) : x = y := by
  funext s
  exact congrArg Subtype.val (hinj s (a₁ := ⟨x s, hx s⟩) (a₂ := ⟨y s, hy s⟩)
    (Subtype.ext (congrFun hxy s)))

omit [LinearOrder σ] [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) 𝒩] in
theorem moduleCechMap_homogeneous_lift (d : ℤ)
    (hsurj : ∀ s : Finset σ, Function.Surjective (moduleCechDegreeMap R ℳ 𝒩 f hf d s))
    (q : ℕ) (y : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R N) (hy : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R N 𝒩 d y)
    (hyc : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R N q y) :
    ∃ x : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d x ∧ ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q x ∧ ModuleCech.Maps.ProjectiveCech.moduleCechMap R f x = y := by
  apply ModuleCech.ExactSequences.ProjectiveCech.moduleCechMap_lift_of_pointwise R ℳ f d q y hyc
  intro s
  obtain ⟨x, hx⟩ := hsurj s ⟨y s, hy s⟩
  exact ⟨x.val, x.property, congrArg Subtype.val hx⟩

omit [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) 𝒩] in
theorem moduleCechExactAt_iff_of_degreeMap_bijective (d : ℤ)
    (hbij : ∀ s : Finset σ, Function.Bijective (moduleCechDegreeMap R ℳ 𝒩 f hf d s)) (q : ℕ) :
    DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q ↔ DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R N 𝒩 d q := by
  constructor
  · intro hM y hy hyc hyd
    obtain ⟨x, hx, hxc, hxf⟩ := moduleCechMap_homogeneous_lift R ℳ 𝒩 f hf d
      (fun s => (hbij s).2) q y hy hyc
    have hxd : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M x = 0 := by
      apply moduleCechMap_homogeneous_injective R ℳ 𝒩 f hf d (fun s => (hbij s).1)
        _ _ (ModuleCech.Card.ProjectiveCech.moduleCechDifferential_homogeneous R M ℳ d x hx) (fun _ => Submodule.zero_mem _)
      change ModuleCech.Maps.ProjectiveCech.moduleCechMap R f (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M x) =
        ModuleCech.Maps.ProjectiveCech.moduleCechMap R f (0 : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
      rw [map_zero, ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, hxf, hyd]
    obtain ⟨a, ha, hac, had⟩ := hM x hx hxc hxd
    refine ⟨ModuleCech.Maps.ProjectiveCech.moduleCechMap R f a, ModuleCech.Maps.ProjectiveCech.moduleCechMap_homogeneous R ℳ 𝒩 f hf d a ha,
      ModuleCech.Maps.ProjectiveCech.moduleCechMap_card R f (q - 1) a hac, ?_⟩
    rw [← ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, had, hxf]
  · intro hN x hx hxc hxd
    have hy := ModuleCech.Maps.ProjectiveCech.moduleCechMap_homogeneous R ℳ 𝒩 f hf d x hx
    have hyc := ModuleCech.Maps.ProjectiveCech.moduleCechMap_card R f q x hxc
    have hyd : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R N (ModuleCech.Maps.ProjectiveCech.moduleCechMap R f x) = 0 := by
      rw [← ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, hxd, map_zero]
    obtain ⟨a, ha, hac, had⟩ := hN _ hy hyc hyd
    obtain ⟨b, hb, hbc, hbf⟩ := moduleCechMap_homogeneous_lift R ℳ 𝒩 f hf d
      (fun s => (hbij s).2) (q - 1) a ha hac
    refine ⟨b, hb, hbc, ?_⟩
    apply moduleCechMap_homogeneous_injective R ℳ 𝒩 f hf d (fun s => (hbij s).1)
      _ _ (ModuleCech.Card.ProjectiveCech.moduleCechDifferential_homogeneous R M ℳ d b hb) hx
    rw [ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, hbf, had]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.DegreeMapExactness.ProjectiveCech
