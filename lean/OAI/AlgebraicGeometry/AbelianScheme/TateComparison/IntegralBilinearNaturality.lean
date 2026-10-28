import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Lean.Util.CollectAxioms

/-! # Integral Bilinear Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralBilinearNaturality

noncomputable section

/-! Scalar extension of an integral bilinear form preserves actual
adjoints and integer multipliers. -/

open scoped TensorProduct

variable {R K V W I : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem integralBilinearBaseChange_similitude (b : Module.Basis I R V)
    (B : LinearMap.BilinForm R V) (C : LinearMap.BilinForm R W)
    (f : V →ₗ[R] W) (n : ℕ) (hf : ∀ x y, C (f x) (f y) = n • B x y)
    (x y : K ⊗[R] V) :
    C.baseChange K (f.baseChange K x) (f.baseChange K y) = n • B.baseChange K x y := by
  have he : (C.baseChange K).compl₁₂ (f.baseChange K) (f.baseChange K) =
      n • B.baseChange K := by
    apply (b.baseChange K).ext
    intro i
    apply (b.baseChange K).ext
    intro j
    change C.baseChange K (f.baseChange K ((b.baseChange K) i))
      (f.baseChange K ((b.baseChange K) j)) =
      n • B.baseChange K ((b.baseChange K) i) ((b.baseChange K) j)
    simp only [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
      LinearMap.BilinForm.baseChange_tmul, one_mul, hf, nsmul_eq_mul]
    simp only [← Algebra.algebraMap_eq_smul_one, map_mul, map_natCast]
  exact LinearMap.congr_fun₂ he x y

theorem integralBilinearBaseChange_adjoint (b : Module.Basis I R V)
    (B : LinearMap.BilinForm R V) (f g : V →ₗ[R] V)
    (hfg : ∀ x y, B (f x) y = B x (g y)) (x y : K ⊗[R] V) :
    B.baseChange K (f.baseChange K x) y = B.baseChange K x (g.baseChange K y) := by
  have he : (B.baseChange K).compl₁₂ (f.baseChange K) LinearMap.id =
      (B.baseChange K).compl₁₂ LinearMap.id (g.baseChange K) := by
    apply (b.baseChange K).ext
    intro i
    apply (b.baseChange K).ext
    intro j
    change B.baseChange K (f.baseChange K ((b.baseChange K) i)) ((b.baseChange K) j) =
      B.baseChange K ((b.baseChange K) i) (g.baseChange K ((b.baseChange K) j))
    simp only [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
      LinearMap.BilinForm.baseChange_tmul, one_mul, hfg]
  exact LinearMap.congr_fun₂ he x y

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralBilinearNaturality
