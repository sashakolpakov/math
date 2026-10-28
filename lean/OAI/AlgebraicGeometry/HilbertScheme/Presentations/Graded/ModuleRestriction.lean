import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.ModuleRestriction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreePieces
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedFreeModules
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentRestriction

/-! # Module Restriction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleRestriction

noncomputable section

/-! Restriction along projective chart inclusions preserves homogeneous module degrees. -/

open _root_.MvPolynomial

namespace GradedModules

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]

theorem awayModuleRestriction_homogeneous (a b c : A) (h : b = a * c)
    (e f : ℤ) (ha : a ∈ 𝒜 e) (hc : c ∈ 𝒜 f) (d : ℤ) (x : Presentations.Module.Fractions.GradedModules.AwayModule a M)
    (hx : x ∈ Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a e d) :
    Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction M a b c h x ∈ Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ b (e + f) d := by
  obtain ⟨k, m, hm, rfl⟩ := (Localized.DegreePieces.GradedModules.mem_localizedDegreePiece_iff 𝒜 ℳ a e ha d x).mp hx
  rw [Presentations.Module.Fractions.GradedModules.moduleFractionMap_apply, Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction_fraction]
  have hpow : c ^ k ∈ 𝒜 ((k : ℤ) * f) := by
    simpa only [nsmul_eq_mul] using SetLike.pow_mem_graded k hc
  have hmem := SetLike.GradedSMul.smul_mem hpow hm
  have heq : (k : ℤ) * f + (d + (k : ℤ) * e) = d + (k : ℤ) * (e + f) := by ring
  have hm' : c ^ k • m ∈ ℳ (d + (k : ℤ) * (e + f)) := heq ▸ hmem
  simpa only [Presentations.Module.Fractions.GradedModules.moduleFractionMap_apply] using
    Localized.DegreePieces.GradedModules.moduleFractionMap_mem_degree ℳ b (e + f) d k (c ^ k • m) hm'

end GradedModules

namespace ProjectiveCech

universe u v w

variable {σ : Type u} [Fintype σ] [DecidableEq σ]
variable (R : Type v) [CommRing R]

omit [Fintype σ] [DecidableEq σ] in
theorem inversionMonomial_integer_degree (s : Finset σ) :
    LaurentMonomials.ProjectiveCech.inversionMonomial R s ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R (s.card : ℤ) := by
  apply isWeightedHomogeneous_monomial
  simp [LaurentExponents.ProjectiveCech.inversionExponent, map_sum, Finsupp.weight_single]

variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

abbrev ModuleChart (s : Finset σ) := Presentations.Module.Fractions.GradedModules.AwayModule (LaurentMonomials.ProjectiveCech.inversionMonomial R s) M

def moduleChartRestriction {s t : Finset σ} (h : s ⊆ t) :
    ModuleChart R M s →ₗ[R] ModuleChart R M t :=
  (Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction M (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (LaurentMonomials.ProjectiveCech.inversionMonomial R t)
    (LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s)) (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R h).symm).restrictScalars R

variable (ℳ : ℤ → Submodule R M)
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

def moduleChartDegree (s : Finset σ) (d : ℤ) : Submodule R (ModuleChart R M s) :=
  Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) d

omit [Fintype σ] in
theorem moduleChartRestriction_degree {s t : Finset σ} (h : s ⊆ t) (d : ℤ)
    (x : ModuleChart R M s) (hx : x ∈ moduleChartDegree R M ℳ s d) :
    moduleChartRestriction R M h x ∈ moduleChartDegree R M ℳ t d := by
  have he : (s.card : ℤ) + ((t \ s).card : ℤ) = (t.card : ℤ) := by
    have hc := Finset.card_sdiff_add_card_eq_card h
    rw [Nat.add_comm] at hc
    exact_mod_cast hc
  have hz := GradedModules.awayModuleRestriction_homogeneous (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ
    (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (LaurentMonomials.ProjectiveCech.inversionMonomial R t) (LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s))
    (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R h).symm (s.card : ℤ) ((t \ s).card : ℤ)
    (inversionMonomial_integer_degree R s) (inversionMonomial_integer_degree R (t \ s)) d x hx
  rw [he] at hz
  exact hz

end ProjectiveCech

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleRestriction
