import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.BilinearMap

/-! # Bilinear Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearQuotient

noncomputable section

/-! Descent of a bilinear map through two module quotients when it
vanishes on each of the specified submodules. -/

variable {R M N L : Type*} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
  [Module R M] [Module R N] [Module R L]

def liftRight (Q : Submodule R N) (B : M →ₗ[R] N →ₗ[R] L)
    (h : ∀ x y, y ∈ Q → B x y = 0) : M →ₗ[R] (N ⧸ Q →ₗ[R] L) where
  toFun x := Q.liftQ (B x) (fun y hy => h x y hy)
  map_add' x x' := by
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ := Q.mkQ_surjective q
    change B (x + x') y = B x y + B x' y
    exact DFunLike.congr_fun (B.map_add x x') y
  map_smul' r x := by
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ := Q.mkQ_surjective q
    change B (r • x) y = r • B x y
    exact DFunLike.congr_fun (B.map_smul r x) y

def lift₂ (P : Submodule R M) (Q : Submodule R N) (B : M →ₗ[R] N →ₗ[R] L)
    (hleft : ∀ x, x ∈ P → ∀ y, B x y = 0)
    (hright : ∀ x y, y ∈ Q → B x y = 0) :
    (M ⧸ P) →ₗ[R] (N ⧸ Q) →ₗ[R] L :=
  P.liftQ (liftRight Q B hright) (by
    intro x hx
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ := Q.mkQ_surjective q
    exact hleft x hx y)

@[simp]
theorem lift₂_mkQ (P : Submodule R M) (Q : Submodule R N) (B : M →ₗ[R] N →ₗ[R] L)
    (hleft : ∀ x, x ∈ P → ∀ y, B x y = 0)
    (hright : ∀ x y, y ∈ Q → B x y = 0) (x : M) (y : N) :
    lift₂ P Q B hleft hright (P.mkQ x) (Q.mkQ y) = B x y := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearQuotient
