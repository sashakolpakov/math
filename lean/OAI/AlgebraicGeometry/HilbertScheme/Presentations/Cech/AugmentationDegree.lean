import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms

/-! # Augmentation Degree -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.AugmentationDegree.ProjectiveCech

noncomputable section

/-! The degree-zero Čech term is the original homogeneous module piece. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u}
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

theorem inversionMonomial_empty : LaurentMonomials.ProjectiveCech.inversionMonomial (σ := σ) R ∅ = 1 := by
  simp [LaurentMonomials.ProjectiveCech.inversionMonomial, LaurentExponents.ProjectiveCech.inversionExponent]

theorem emptyChart_fraction (k : ℕ) (m : M) :
    Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial (σ := σ) R ∅) k m =
      Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial (σ := σ) R ∅) 0 m := by
  have h := Presentations.Module.Fractions.GradedModules.moduleFractionMap_raise (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial (σ := σ) R ∅) 0 k m
  simpa only [Nat.zero_add, inversionMonomial_empty, one_pow, one_smul] using h

def emptyModuleChartEquiv : M ≃ₗ[R] Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := σ) R M ∅ :=
  LinearEquiv.ofBijective (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial (σ := σ) R ∅) 0) ⟨by
    intro x y hxy
    have hz : Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial (σ := σ) R ∅) 0 (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨l, hl⟩ := (Presentations.Module.Fractions.GradedModules.moduleFractionMap_eq_zero (R := R) _ 0 _).mp hz
    simp only [inversionMonomial_empty, one_pow, one_smul] at hl
    exact sub_eq_zero.mp hl, by
    intro x
    obtain ⟨k, m, hm⟩ := Presentations.Module.Fractions.GradedModules.moduleFractionMap_surj (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial (σ := σ) R ∅) x
    exact ⟨m, (emptyChart_fraction R M k m).symm.trans hm⟩⟩

variable (ℳ : ℤ → Submodule R M)
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

theorem emptyModuleChartEquiv_degree (d : ℤ) (m : M) :
    emptyModuleChartEquiv (σ := σ) R M m ∈ Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree (σ := σ) R M ℳ ∅ d ↔ m ∈ ℳ d := by
  constructor
  · intro hx
    obtain ⟨k, n, hn, he⟩ := (Localized.DegreePieces.GradedModules.mem_localizedDegreePiece_iff (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ
      (LaurentMonomials.ProjectiveCech.inversionMonomial R ∅) (∅ : Finset σ).card (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R ∅) d _).mp hx
    rw [emptyChart_fraction R M k n] at he
    have hnm : n = m := (emptyModuleChartEquiv (σ := σ) R M).injective he
    simpa only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero, hnm] using hn
  · intro hm
    apply Localized.DegreePieces.GradedModules.moduleFractionMap_mem_degree ℳ _ _ d 0 m
    simpa only [Nat.cast_zero, zero_mul, add_zero] using hm

def emptyModuleChartDegreeEquiv (d : ℤ) : ℳ d ≃ₗ[R] Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree (σ := σ) R M ℳ ∅ d :=
  LinearEquiv.ofBijective
    (((emptyModuleChartEquiv (σ := σ) R M).toLinearMap.comp (ℳ d).subtype).codRestrict
      (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree (σ := σ) R M ℳ ∅ d) (fun m => (emptyModuleChartEquiv_degree (σ := σ) R M ℳ d m.val).mpr m.property))
    ⟨by
      intro x y hxy
      apply Subtype.ext
      apply (emptyModuleChartEquiv (σ := σ) R M).injective
      exact congrArg (fun z : Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree (σ := σ) R M ℳ ∅ d => z.val) hxy, by
      intro x
      let m := (emptyModuleChartEquiv (σ := σ) R M).symm x.val
      have hm : m ∈ ℳ d := (emptyModuleChartEquiv_degree (σ := σ) R M ℳ d m).mp
        (by simpa only [m, LinearEquiv.apply_symm_apply] using x.property)
      exact ⟨⟨m, hm⟩, Subtype.ext ((emptyModuleChartEquiv (σ := σ) R M).apply_symm_apply x.val)⟩⟩

def moduleCechAugmentationEquiv (d : ℤ) : ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d 0 ≃ₗ[R] ℳ d := by
  let : Unique {s : Finset σ // s.card = 0} :=
    { default := ⟨∅, Finset.card_empty⟩
      uniq := fun s => Subtype.ext (Finset.card_eq_zero.mp s.property) }
  exact (ModuleCech.Terms.ProjectiveCech.moduleCechTermEquiv (σ := σ) R M ℳ d 0).trans
    ((LinearEquiv.piUnique R (fun s : {s : Finset σ // s.card = 0} => Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree (σ := σ) R M ℳ s.val d)).trans
      (emptyModuleChartDegreeEquiv (σ := σ) R M ℳ d).symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.AugmentationDegree.ProjectiveCech
