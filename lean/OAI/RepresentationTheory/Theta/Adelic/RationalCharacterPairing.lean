import OAI.RepresentationTheory.Theta.Adelic.GlobalCharacterNontrivial
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanDualLattice

/-! # Rational Character Pairing -/

namespace OAI.RepresentationTheory.Theta.Adelic.RationalCharacterPairing

noncomputable section

/-! A nonzero rational archimedean character has nondegenerate pairing.
The field multiplication argument supplies the missing nondegeneracy; no
local splitting or assumed local character nontriviality is used. -/

open scoped _root_.NumberField Classical
open _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanDualLattice.Construction

variable (F : Type) [Field F] [NumberField F]

theorem rational_functional
    (L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hrat : ∀ r : 𝓞 F, ∃ q : ℚ,
      (q : ℝ) = L (mixedEmbedding F (algebraMap (𝓞 F) F r))) :
    ∃ ℓ : F →ₗ[ℚ] ℚ, ∀ q : F, (ℓ q : ℝ) = L (mixedEmbedding F q) := by
  choose a ha using fun i => hrat (RingOfIntegers.basis F i)
  let ℓ : F →ₗ[ℚ] ℚ := (integralBasis F).constr ℚ a
  let A : F →ₗ[ℚ] ℝ := (Algebra.linearMap ℚ ℝ).comp ℓ
  let B : F →ₗ[ℚ] ℝ := (L.restrictScalars ℚ).comp (mixedEmbedding F).toAddMonoidHom.toRatLinearMap
  have he : A = B := by
    apply (integralBasis F).ext
    intro i
    change (ℓ (integralBasis F i) : ℝ) = L (mixedEmbedding F (integralBasis F i))
    rw [show ℓ (integralBasis F i) = a i from (integralBasis F).constr_basis ℚ a i]
    simpa only [integralBasis_apply] using ha i
  exact ⟨ℓ, fun q => DFunLike.congr_fun he q⟩

theorem linear_pairing_nondegenerate
    (L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (hL : L ≠ 0)
    (hrat : ∀ r : 𝓞 F, ∃ q : ℚ,
      (q : ℝ) = L (mixedEmbedding F (algebraMap (𝓞 F) F r))) :
    ∀ x : mixedEmbedding.mixedSpace F, (∀ y, L (x * y) = 0) → x = 0 := by
  obtain ⟨ℓ, hℓ⟩ := rational_functional F L hrat
  have hℓ0 : ℓ ≠ 0 := by
    intro hz
    apply hL
    apply (mixedEmbedding.latticeBasis F).ext
    intro i
    change L (mixedEmbedding.latticeBasis F i) = 0
    rw [mixedEmbedding.latticeBasis_apply, ← hℓ, hz, LinearMap.zero_apply, Rat.cast_zero]
  have hnonzero : ∃ a : F, ℓ a ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hℓ0 (LinearMap.ext h)
  let B : LinearMap.BilinForm ℚ F := (LinearMap.mul ℚ F).compr₂ ℓ
  have hB : B.Nondegenerate := by
    have hleft : ∀ x : F, (∀ y, ℓ (x * y) = 0) → x = 0 := by
      intro x hx
      by_contra hx0
      obtain ⟨a, ha⟩ := hnonzero
      have he := hx (x⁻¹ * a)
      rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at he
      exact ha he
    refine ⟨hleft, ?_⟩
    intro y hy
    apply hleft y
    intro x
    have he := hy x
    change ℓ (x * y) = 0 at he
    simpa only [mul_comm] using he
  let A := LinearMap.BilinForm.toMatrix (integralBasis F) B
  have hA : A.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (integralBasis F)).mp hB
  let BR : LinearMap.BilinForm ℝ (mixedEmbedding.mixedSpace F) := (LinearMap.mul ℝ _).compr₂ L
  have hm : LinearMap.BilinForm.toMatrix (mixedEmbedding.latticeBasis F) BR =
      A.map (algebraMap ℚ ℝ) := by
    apply Matrix.ext
    intro i j
    simp only [A, Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply]
    change L (mixedEmbedding.latticeBasis F i * mixedEmbedding.latticeBasis F j) =
      (ℓ (integralBasis F i * integralBasis F j) : ℝ)
    rw [mixedEmbedding.latticeBasis_apply, mixedEmbedding.latticeBasis_apply, ← map_mul, hℓ]
  have hBR : BR.Nondegenerate := by
    apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (mixedEmbedding.latticeBasis F)).mpr
    rw [hm]
    change ((algebraMap ℚ ℝ).mapMatrix A).det ≠ 0
    rw [← RingHom.map_det]
    exact (map_ne_zero_iff _ (algebraMap ℚ ℝ).injective).mpr hA
  exact hBR.1

end

end OAI.RepresentationTheory.Theta.Adelic.RationalCharacterPairing
