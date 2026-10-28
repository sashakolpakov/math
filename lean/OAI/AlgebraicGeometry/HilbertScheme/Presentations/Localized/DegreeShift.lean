import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ShiftEquiv
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.ModuleRestriction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.Grading
import Mathlib.RingTheory.Flat.Basic

/-! # Degree Shift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreeShift.GradedModules

noncomputable section

/-! An invertible homogeneous scalar identifies shifted localization degrees. -/

open DirectSum

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]

def localizedScalarEnd (g b : A) : Presentations.Module.Fractions.GradedModules.AwayModule g M →ₗ[R] Presentations.Module.Fractions.GradedModules.AwayModule g M :=
  (algebraMap A (Module.End A (Presentations.Module.Fractions.GradedModules.AwayModule g M)) b).restrictScalars R

theorem localizedScalarEnd_homogeneous (g : A) (e : ℤ) (hg : g ∈ 𝒜 e)
    (b : A) (t : ℤ) (hb : b ∈ 𝒜 t) (d : ℤ) (x : Presentations.Module.Fractions.GradedModules.AwayModule g M)
    (hx : x ∈ DegreePieces.GradedModules.localizedDegreePiece ℳ g e d) :
    localizedScalarEnd (R := R) (M := M) g b x ∈ DegreePieces.GradedModules.localizedDegreePiece ℳ g e (d + t) := by
  obtain ⟨k, m, hm, rfl⟩ := (DegreePieces.GradedModules.mem_localizedDegreePiece_iff 𝒜 ℳ g e hg d x).mp hx
  change b • Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) g k m ∈ _
  rw [Presentations.Module.Fractions.GradedModules.moduleFractionMap_apply, LocalizedModule.smul'_mk]
  have hm' := SetLike.GradedSMul.smul_mem hb hm
  have he : t + (d + (k : ℤ) * e) = d + t + (k : ℤ) * e := by ring
  have hmem := DegreePieces.GradedModules.moduleFractionMap_mem_degree ℳ g e (d + t) k (b • m) (he ▸ hm')
  simpa only [Presentations.Module.Fractions.GradedModules.moduleFractionMap_apply] using hmem

def localizedScalarPowerEquiv (g b c : A) (h : g = b * c) (k : ℕ) :
    Presentations.Module.Fractions.GradedModules.AwayModule g M ≃ₗ[R] Presentations.Module.Fractions.GradedModules.AwayModule g M :=
  LinearEquiv.ofBijective (localizedScalarEnd (R := R) (M := M) g (b ^ k)) (by
    have hu := (Presentations.Module.ModuleRestriction.GradedModules.awayModuleFactor_isUnit M b g c h).pow k
    rw [← map_pow] at hu
    exact (Module.End.isUnit_iff (algebraMap A (Module.End A (Presentations.Module.Fractions.GradedModules.AwayModule g M)) (b ^ k))).mp hu)

variable [Decomposition ℳ]

theorem localizedDegree_flat_of_degree_zero (g : A) (e : ℤ) (hg : g ∈ 𝒜 e)
    (b c : A) (h : g = b * c) (hb : b ∈ 𝒜 1) (k : ℕ)
    [Module.Flat R (DegreePieces.GradedModules.localizedDegreePiece ℳ g e 0)] :
    Module.Flat R (DegreePieces.GradedModules.localizedDegreePiece ℳ g e (k : ℤ)) := by
  let := Grading.GradedModules.localizedDegreeDecomposition 𝒜 ℳ g e hg
  have hpow : b ^ k ∈ 𝒜 (k : ℤ) := by
    simpa only [nsmul_eq_mul, mul_one] using SetLike.pow_mem_graded k hb
  let F := localizedScalarPowerEquiv (R := R) (M := M) g b c h k
  have hF : ∀ d x, x ∈ DegreePieces.GradedModules.localizedDegreePiece ℳ g e d → F x ∈ DegreePieces.GradedModules.localizedDegreePiece ℳ g e (d + k) :=
    localizedScalarEnd_homogeneous 𝒜 ℳ g e hg (b ^ k) (k : ℤ) hpow
  let E := Graded.ShiftEquiv.GradedModules.gradedShiftEquiv (DegreePieces.GradedModules.localizedDegreePiece ℳ g e) F (k : ℤ) hF 0
  let : Module.Flat R (DegreePieces.GradedModules.localizedDegreePiece ℳ g e (0 + k)) := Module.Flat.of_linearEquiv E.symm
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofEq _ _
    (congrArg (DegreePieces.GradedModules.localizedDegreePiece ℳ g e) (zero_add (k : ℤ))).symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreeShift.GradedModules
