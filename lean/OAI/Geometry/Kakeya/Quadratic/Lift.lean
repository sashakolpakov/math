import OAI.Analysis.Fourier.Estimates
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Explicit linear ruling of the quadratic-curve lift.  The auxiliary
space is the actual range of B, so no choice of a rank factorization is
needed.  This is the quadratic case of Nadjimzadah's lifting construction. -/

open Set Module
open scoped Topology ContDiff

noncomputable section
namespace OAI.Geometry.Kakeya.Quadratic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def curve (B : E →ₗ[ℝ] E) (y w : E) (t : ℝ) : E × ℝ :=
  (w + t • y + (t ^ 2) • B y, t)

def slope (B : E →ₗ[ℝ] E) : E × LinearMap.range B →ₗ[ℝ] E × LinearMap.range B where
  toFun p := (p.1 - (p.2 : E), B.rangeRestrict p.1)
  map_add' p q := by ext <;> simp [sub_add_sub_comm]
  map_smul' c p := by ext <;> simp [smul_sub]

def liftProjection (B : E →ₗ[ℝ] E) (p : (E × LinearMap.range B) × ℝ) : E × ℝ :=
  (p.1.1 + p.2 • (p.1.2 : E), p.2)

def liftedLine (B : E →ₗ[ℝ] E) (y w : E) (z : LinearMap.range B) (t : ℝ) :
    (E × LinearMap.range B) × ℝ :=
  ((w, z) + t • slope B (y, z), t)

omit [FiniteDimensional ℝ E] in
theorem liftProjection_liftedLine (B : E →ₗ[ℝ] E) (y w : E)
    (z : LinearMap.range B) (t : ℝ) :
    liftProjection B (liftedLine B y w z t) = curve B y w t := by
  apply Prod.ext
  · change w + t • (y - (z : E)) + t • ((z : E) + t • B y) =
      w + t • y + (t ^ 2) • B y
    simp only [smul_sub, smul_add, smul_smul, pow_two]
    abel
  · rfl

/-- The lift is a global smooth shear of a product, not merely a local
submersion.  This is useful for the Hausdorff-dimension comparison. -/
def liftShear (B : E →ₗ[ℝ] E) :
    ((E × LinearMap.range B) × ℝ) ≃ₜ ((E × ℝ) × LinearMap.range B) where
  toFun p := (liftProjection B p, p.1.2)
  invFun p := ((p.1.1 - p.1.2 • (p.2 : E), p.2), p.1.2)
  left_inv p := by ext <;> simp [liftProjection]
  right_inv p := by ext <;> simp [liftProjection]
  continuous_toFun := by unfold liftProjection; fun_prop
  continuous_invFun := by fun_prop

omit [FiniteDimensional ℝ E] in
theorem contDiff_liftShear (B : E →ₗ[ℝ] E) : ContDiff ℝ ∞ (liftShear B) := by
  have hc : ContDiff ℝ ∞ (fun z : B.range => (z : E)) := B.range.subtypeL.contDiff
  change ContDiff ℝ ∞ (fun p : (E × LinearMap.range B) × ℝ =>
    ((p.1.1 + p.2 • (p.1.2 : E), p.2), p.1.2))
  fun_prop

omit [FiniteDimensional ℝ E] in
theorem contDiff_liftShear_symm (B : E →ₗ[ℝ] E) :
    ContDiff ℝ ∞ (liftShear B).symm := by
  have hc : ContDiff ℝ ∞ (fun z : B.range => (z : E)) := B.range.subtypeL.contDiff
  change ContDiff ℝ ∞ (fun p : (E × ℝ) × LinearMap.range B =>
    ((p.1.1 - p.1.2 • (p.2 : E), p.2), p.1.2))
  fun_prop

/-- The kernel of the lifted slope map is exactly ker B intersect range B. -/
def slopeKerEquiv (B : E →ₗ[ℝ] E) :
    LinearMap.ker (slope B) ≃ₗ[ℝ] (LinearMap.ker B ⊓ LinearMap.range B : Submodule ℝ E) where
  toFun p := ⟨p.1.1, by
    have h := p.2
    change (p.1.1 - (p.1.2 : E), B.rangeRestrict p.1.1) = 0 at h
    constructor
    · exact congrArg (fun z : E × LinearMap.range B => (z.2 : E)) h
    · have he := congrArg Prod.fst h
      have he' : p.1.1 = (p.1.2 : E) := sub_eq_zero.mp he
      exact he' ▸ p.1.2.2⟩
  invFun p := ⟨(p.1, ⟨p.1, p.2.2⟩), by
    change (p.1 - p.1, B.rangeRestrict p.1) = 0
    apply Prod.ext
    · simp
    · apply Subtype.ext
      exact p.2.1⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      have h := congrArg Prod.fst p.2
      exact sub_eq_zero.mp h
  right_inv p := rfl
  map_add' p q := rfl
  map_smul' c p := rfl

def restrictedKerEquiv (B : E →ₗ[ℝ] E) :
    LinearMap.ker (B.comp (LinearMap.range B).subtype) ≃ₗ[ℝ]
      (LinearMap.ker B ⊓ LinearMap.range B : Submodule ℝ E) where
  toFun p := ⟨p.1.1, p.2, p.1.2⟩
  invFun p := ⟨⟨p.1, p.2.2⟩, p.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional ℝ E] in
theorem range_restricted (B : E →ₗ[ℝ] E) :
    LinearMap.range (B.comp (LinearMap.range B).subtype) =
      LinearMap.range (B.comp B) := by
  ext x
  constructor
  · rintro ⟨⟨y, z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨⟨B y, y, rfl⟩, rfl⟩

/-- The lifted directions have exactly dim E + rank(B²) degrees of
freedom.  This is the dimension used in the linear Kakeya input. -/
theorem finrank_slope_range (B : E →ₗ[ℝ] E) :
    finrank ℝ (LinearMap.range (slope B)) =
      finrank ℝ E + finrank ℝ (LinearMap.range (B.comp B)) := by
  have h₁ := (slope B).finrank_range_add_finrank_ker
  have h₂ := (B.comp (LinearMap.range B).subtype).finrank_range_add_finrank_ker
  rw [Module.finrank_prod, (slopeKerEquiv B).finrank_eq] at h₁
  rw [range_restricted, (restrictedKerEquiv B).finrank_eq] at h₂
  omega

end OAI.Geometry.Kakeya.Quadratic
