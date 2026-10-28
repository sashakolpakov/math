import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeCommutation

/-! # Hecke Scalar Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalarNaturality.GeneralizedHecke

noncomputable section

section

/-! Comparison naturality for rational weighted sums after genuine coefficient extension. -/

open scoped TensorProduct

variable {K L V W I : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]

theorem baseChange_weighted_sum (s : I →₀ K) (T : I → Module.End K V) :
    (s.sum (fun i a => a • T i)).baseChange L =
      s.sum (fun i a => algebraMap K L a • (T i).baseChange L) := by
  classical
  change (Module.End.baseChangeHom K L V) (s.sum (fun i a => a • T i)) = _
  simp only [Finsupp.sum, map_sum, map_smul, IsScalarTower.algebraMap_smul]
  rfl

theorem weighted_scalar_naturality (e : (L ⊗[K] V) ≃ₗ[L] W)
    (s : I →₀ K) (T : I → Module.End K V) (U : I → Module.End L W)
    (h : ∀ i x, e ((T i).baseChange L x) = U i (e x)) (x : L ⊗[K] V) :
    e ((s.sum (fun i a => a • T i)).baseChange L x) =
      (s.sum (fun i a => algebraMap K L a • U i)) (e x) := by
  classical
  rw [baseChange_weighted_sum]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun y => algebraMap K L (s i) • y) (h i x))

end

/-! Rational combinations of geometric operators intertwine under a genuine scalar comparison. -/

open scoped TensorProduct

variable {K L V W I : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]

theorem baseChange_rational_weighted_sum (s : I →₀ ℚ) (T : I → Module.End K V) :
    (s.sum (fun i a => (a : K) • T i)).baseChange L =
      s.sum (fun i a => (a : L) • (T i).baseChange L) := by
  classical
  change (Module.End.baseChangeHom K L V) (s.sum (fun i a => (a : K) • T i)) = _
  simp only [Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact (IsScalarTower.algebraMap_smul L (s i : K) ((T i).baseChange L)).symm.trans
    (congrArg (fun c : L => c • (T i).baseChange L) (map_ratCast (algebraMap K L) (s i)))

theorem rational_weighted_scalar_naturality (e : (L ⊗[K] V) ≃ₗ[L] W)
    (s : I →₀ ℚ) (T : I → Module.End K V) (U : I → Module.End L W)
    (h : ∀ i x, e ((T i).baseChange L x) = U i (e x)) (x : L ⊗[K] V) :
    e ((s.sum (fun i a => (a : K) • T i)).baseChange L x) =
      (s.sum (fun i a => (a : L) • U i)) (e x) := by
  classical
  rw [baseChange_rational_weighted_sum]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun y => (s i : L) • y) (h i x))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalarNaturality.GeneralizedHecke
