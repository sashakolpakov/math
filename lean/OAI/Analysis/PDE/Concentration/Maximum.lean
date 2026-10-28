import OAI.Analysis.PDE.Concentration.Cylinder.Coordinates
import OAI.Analysis.PDE.Concentration.SmoothExtension

namespace OAI.Analysis.PDE.Concentration

open Set Filter Laplacian InnerProductSpace
open scoped ContDiff Topology

theorem laplacian_maximum {f : CylinderSpace → ℝ} {K : Set CylinderSpace} {M : ℝ}
    (hK : IsCompact K) (hf : ContDiff ℝ 2 f)
    (hΔ : ∀ x ∈ interior K, 0 ≤ Δ f x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ M) : ∀ x ∈ K, f x ≤ M := by
  apply OAI.Analysis.PDE.Dirichlet.maximum_principle (a := fun _ (_ : Fin 3) => (1 : ℝ))
    (v := fun _ => EuclideanSpace.basisFun (Fin 3) ℝ) hK hf
  · intro x hx i
    norm_num
  · intro x hx
    simp only [OrthonormalBasis.norm_eq_one, one_pow, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num
  · intro x hx
    have h := hΔ x hx
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 3) ℝ)] at h
    simpa only [OAI.Analysis.PDE.Dirichlet.ellipticValue, one_mul, iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] using h
  · exact hbd

theorem laplacian_maximum_on {f : CylinderSpace → ℝ} {K U : Set CylinderSpace} {M : ℝ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hf : ContDiffOn ℝ ∞ f U)
    (hΔ : ∀ x ∈ interior K, 0 ≤ Δ f x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ M) : ∀ x ∈ K, f x ≤ M := by
  obtain ⟨F, hF, he⟩ := exists_global_smooth_eq_near_closed hK.isClosed hU hKU hf
  have hbound := laplacian_maximum hK (hF.of_le (by simp)) (fun x hx => by
    rw [(laplacian_congr_nhds (he x (interior_subset hx))).self_of_nhds]
    exact hΔ x hx) (fun x hx hxi => by rw [(he x hx).self_of_nhds]; exact hbd x hx hxi)
  intro x hx
  have h := hbound x hx
  rwa [(he x hx).self_of_nhds] at h

end OAI.Analysis.PDE.Concentration
