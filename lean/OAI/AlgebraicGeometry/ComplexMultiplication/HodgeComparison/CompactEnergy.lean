import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Compact Energy -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactEnergy.CM.Construction

noncomputable section

/-! Weak elliptic inversion from a compact lower-order inclusion and the graph inner product. -/

open _root_.Module InnerProductSpace _root_.ContinuousLinearMap
open scoped InnerProduct

variable {𝕜 V H W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- In a graph Hilbert norm, the energy operator is identity minus a compact operator. -/
theorem graphEnergy_eq_identity_sub (J : V →L[𝕜] H) (D : V →L[𝕜] W)
    (hgraph : ∀ u v, ⟪u, v⟫ = ⟪J u, J v⟫ + ⟪D u, D v⟫) :
    D.adjoint.comp D = 1 - J.adjoint.comp J := by
  ext u
  apply ext_inner_right 𝕜
  intro v
  simp only [comp_apply, sub_apply, inner_sub_left, adjoint_inner_left]
  change ⟪D u, D v⟫ = ⟪u, v⟫ - ⟪J u, J v⟫
  rw [hgraph]
  abel

/-- Compactness supplies invertibility of the energy operator once its derivative has zero kernel. -/
theorem graphEnergy_bijective (J : V →L[𝕜] H) (D : V →L[𝕜] W)
    (hJ : IsCompactOperator J) (hD : Function.Injective D)
    (hgraph : ∀ u v, ⟪u, v⟫ = ⟪J u, J v⟫ + ⟪D u, D v⟫) :
    Function.Bijective (D.adjoint.comp D) := by
  let K : V →L[𝕜] V := J.adjoint.comp J
  have hK : IsCompactOperator K := hJ.clm_comp J.adjoint
  have hno : ¬ Module.End.HasEigenvalue (K : Module.End 𝕜 V) 1 := by
    intro heigen
    obtain ⟨u, hu⟩ := heigen.exists_hasEigenvector
    have heq : K u = u := by
      have h := hu.apply_eq_smul
      change K u = (1 : 𝕜) • u at h
      simpa only [one_smul] using h
    have hzero : (D.adjoint.comp D) u = 0 := by
      rw [graphEnergy_eq_identity_sub J D hgraph]
      change u - K u = 0
      rw [heq, sub_self]
    have hinj := (D.adjoint_comp_self_injective_iff).mpr hD
    apply hu.2
    apply hinj
    change (D.adjoint.comp D) u = (D.adjoint.comp D) 0
    simpa only [map_zero] using hzero
  have hres := (hK.hasEigenvalue_or_mem_resolventSet (by norm_num : (1 : 𝕜) ≠ 0)).resolve_left hno
  have hunit : IsUnit (1 - K) := by
    simpa only [spectrum.mem_resolventSet_iff, map_one] using hres
  rw [graphEnergy_eq_identity_sub J D hgraph]
  exact ContinuousLinearMap.isUnit_iff_bijective.mp hunit

/-- Every bounded functional has a unique weak solution when the energy derivative is injective. -/
theorem graphEnergy_weak_existsUnique (J : V →L[𝕜] H) (D : V →L[𝕜] W)
    (hJ : IsCompactOperator J) (hD : Function.Injective D)
    (hgraph : ∀ u v, ⟪u, v⟫ = ⟪J u, J v⟫ + ⟪D u, D v⟫)
    (ℓ : V →L[𝕜] 𝕜) : ∃! u : V, ∀ v : V, ⟪D u, D v⟫ = ℓ v := by
  obtain ⟨u, hu⟩ := (graphEnergy_bijective J D hJ hD hgraph).surjective
    ((InnerProductSpace.toDual 𝕜 V).symm ℓ)
  refine ⟨u, ?_, ?_⟩
  · intro v
    rw [← adjoint_inner_left D, ← comp_apply, hu, InnerProductSpace.toDual_symm_apply]
  · intro u' hu'
    apply (graphEnergy_bijective J D hJ hD hgraph).injective
    apply ext_inner_right 𝕜
    intro v
    rw [hu, InnerProductSpace.toDual_symm_apply]
    simpa only [comp_apply, adjoint_inner_left] using hu' v

omit [CompleteSpace V] [CompleteSpace W] in
/-- The derivative is injective on the orthogonal complement of its actual kernel. -/
theorem derivative_injective_on_kernel_orthogonal (D : V →L[𝕜] W) :
    Function.Injective (D.comp (D.ker)ᗮ.subtypeL) := by
  have hzero : ∀ u : (D.ker)ᗮ, D u.val = 0 → u = 0 := by
    intro u hu
    apply Subtype.ext
    apply (inner_self_eq_zero (𝕜 := 𝕜)).mp
    exact Submodule.inner_right_of_mem_orthogonal (show u.val ∈ D.ker from hu) u.property
  intro u v huv
  apply sub_eq_zero.mp
  apply hzero
  change D (u.val - v.val) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr huv

/-- A functional vanishing on the derivative kernel has a unique normalized weak solution. -/
theorem graphEnergy_weak_existsUnique_orthogonal (J : V →L[𝕜] H) (D : V →L[𝕜] W)
    (hJ : IsCompactOperator J)
    (hgraph : ∀ u v, ⟪u, v⟫ = ⟪J u, J v⟫ + ⟪D u, D v⟫)
    (ℓ : V →L[𝕜] 𝕜) (hℓ : ∀ u ∈ D.ker, ℓ u = 0) :
    ∃! u : (D.ker)ᗮ, ∀ v : V, ⟪D u.val, D v⟫ = ℓ v := by
  let Q := (D.ker)ᗮ
  let JQ := J.comp Q.subtypeL
  let DQ := D.comp Q.subtypeL
  let ℓQ := ℓ.comp Q.subtypeL
  have hgraphQ : ∀ u v : Q, ⟪u, v⟫ = ⟪JQ u, JQ v⟫ + ⟪DQ u, DQ v⟫ := by
    intro u v
    exact hgraph u.val v.val
  obtain ⟨u, hu, huniq⟩ := graphEnergy_weak_existsUnique JQ DQ
    (hJ.comp_clm Q.subtypeL) (derivative_injective_on_kernel_orthogonal D) hgraphQ ℓQ
  refine ⟨u, ?_, ?_⟩
  · intro v
    have : CompleteSpace D.ker := D.isClosed_ker.completeSpace_coe
    obtain ⟨k, hk, q, hq, rfl⟩ := D.ker.exists_add_mem_mem_orthogonal v
    have hkD : D k = 0 := hk
    have hqeq : ⟪D u.val, D q⟫ = ℓ q := hu ⟨q, hq⟩
    rw [map_add, hkD, zero_add, map_add, hℓ k hk, zero_add]
    exact hqeq
  · intro u' hu'
    apply huniq
    intro v
    exact hu' v.val

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactEnergy.CM.Construction
