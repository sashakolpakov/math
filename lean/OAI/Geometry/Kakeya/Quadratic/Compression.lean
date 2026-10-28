import OAI.Geometry.Kakeya.Quadratic.Lift
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Quotient

/-! A coordinate-free construction of the sharp quadratic compression.
It replaces the nilpotent Jordan-block computation by quotient maps. -/

open Set Module LinearMap
open scoped Topology ContDiff

noncomputable section
namespace OAI.Geometry.Kakeya.Quadratic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def compressionSubspace (B : E →ₗ[ℝ] E) : Submodule ℝ E := B.ker ⊔ B.range

abbrev CompressionSpace (B : E →ₗ[ℝ] E) := E ⧸ compressionSubspace B

theorem finrank_compressionSpace (B : E →ₗ[ℝ] E) :
    finrank ℝ (CompressionSpace B) = finrank ℝ B.range - finrank ℝ (B.comp B).range := by
  have h₁ := B.finrank_range_add_finrank_ker
  have h₂ := (B.comp B.range.subtype).finrank_range_add_finrank_ker
  rw [range_restricted, (restrictedKerEquiv B).finrank_eq] at h₂
  have h₃ := Submodule.finrank_sup_add_finrank_inf_eq B.ker B.range
  have h₄ := Submodule.finrank_quotient_add_finrank (compressionSubspace B)
  change finrank ℝ (CompressionSpace B) + finrank ℝ (B.ker ⊔ B.range : Submodule ℝ E) = _ at h₄
  omega

omit [FiniteDimensional ℝ E] in
theorem compression_quotient_B (B : E →ₗ[ℝ] E) (x : E) :
    (compressionSubspace B).mkQ (B x) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (show B.range ≤ compressionSubspace B from le_sup_right) (mem_range_self B x)

/-- There is P with P B = Q, where Q is the quotient by ker B + range B. -/
theorem exists_compression_first (B : E →ₗ[ℝ] E) :
    ∃ P : E →ₗ[ℝ] CompressionSpace B,
      P.comp B = (compressionSubspace B).mkQ := by
  let Q := (compressionSubspace B).mkQ
  obtain ⟨r, hr⟩ := B.rangeRestrict.exists_rightInverse_of_surjective B.range_rangeRestrict
  obtain ⟨P, hP⟩ := (Q.comp r).exists_extend
  refine ⟨P, ?_⟩
  ext x
  have hPr : P (B x) = Q (r (B.rangeRestrict x)) :=
    congrArg (fun f : B.range →ₗ[ℝ] CompressionSpace B => f (B.rangeRestrict x)) hP
  rw [LinearMap.comp_apply, hPr]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (show B.ker ≤ compressionSubspace B from le_sup_left)
  change B (r (B.rangeRestrict x) - x) = 0
  rw [map_sub]
  apply sub_eq_zero.mpr
  exact congrArg (fun f : B.range →ₗ[ℝ] B.range => (f (B.rangeRestrict x) : E)) hr

omit [FiniteDimensional ℝ E] in
/-- The two row families are jointly independent. -/
theorem compression_pair_surjective (B : E →ₗ[ℝ] E)
    (P : E →ₗ[ℝ] CompressionSpace B) (hP : P.comp B = (compressionSubspace B).mkQ) :
    Function.Surjective (P.prod (compressionSubspace B).mkQ) := by
  rintro ⟨a, b⟩
  obtain ⟨x, hx⟩ := (compressionSubspace B).mkQ_surjective b
  obtain ⟨y, hy⟩ := (compressionSubspace B).mkQ_surjective (a - P x)
  refine ⟨x + B y, ?_⟩
  apply Prod.ext
  · change P (x + B y) = a
    have hPy : P (B y) = (compressionSubspace B).mkQ y :=
      congrArg (fun f : E →ₗ[ℝ] CompressionSpace B => f y) hP
    rw [map_add, hPy, hy]
    abel
  · change (compressionSubspace B).mkQ (x + B y) = b
    rw [map_add, compression_quotient_B, add_zero, hx]

/-- The sharp compression maps, constructed for every real linear B. -/
theorem exists_compression_maps (B : E →ₗ[ℝ] E) :
    ∃ (P : E →ₗ[ℝ] CompressionSpace B) (C : E →ₗ[ℝ] E),
      P.comp B = (compressionSubspace B).mkQ ∧
      P.comp C = 0 ∧ (compressionSubspace B).mkQ.comp C = P ∧
      Function.Surjective (P.prod (compressionSubspace B).mkQ) := by
  obtain ⟨P, hP⟩ := exists_compression_first B
  have hsur := compression_pair_surjective B P hP
  obtain ⟨R, hR⟩ := (P.prod (compressionSubspace B).mkQ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsur)
  let C : E →ₗ[ℝ] E := R.comp ((0 : E →ₗ[ℝ] CompressionSpace B).prod P)
  refine ⟨P, C, hP, ?_, ?_, hsur⟩
  · ext x
    exact congrArg (fun f : CompressionSpace B × CompressionSpace B →ₗ[ℝ]
      CompressionSpace B × CompressionSpace B => (f (0, P x)).1) hR
  · ext x
    exact congrArg (fun f : CompressionSpace B × CompressionSpace B →ₗ[ℝ]
      CompressionSpace B × CompressionSpace B => (f (0, P x)).2) hR

omit [FiniteDimensional ℝ E] in
/-- Every curve in the explicit compact example lies in the ruled
codimension-d set P(x)=t Q(x). -/
theorem compressed_curve_equation (B : E →ₗ[ℝ] E)
    (P : E →ₗ[ℝ] CompressionSpace B) (C : E →ₗ[ℝ] E)
    (hPB : P.comp B = (compressionSubspace B).mkQ)
    (hPC : P.comp C = 0) (hQC : (compressionSubspace B).mkQ.comp C = P)
    (y : E) (t : ℝ) :
    P (curve B y (C y) t).1 = t • (compressionSubspace B).mkQ (curve B y (C y) t).1 := by
  have h₁ : P (B y) = (compressionSubspace B).mkQ y := congrArg (fun f => f y) hPB
  have h₂ : P (C y) = 0 := congrArg (fun f => f y) hPC
  have h₃ : (compressionSubspace B).mkQ (C y) = P y := congrArg (fun f => f y) hQC
  simp only [curve, map_add, map_smul, h₁, h₂, h₃, compression_quotient_B,
    smul_zero, zero_add, add_zero, smul_add, smul_smul, pow_two]

end OAI.Geometry.Kakeya.Quadratic
