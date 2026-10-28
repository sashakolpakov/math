import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearQuotient

/-! # Ideal Quotient Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotientProduct

noncomputable section

/-! A bilinear product descends through the actual coefficient-ideal
quotients, and all product-preserving linear maps descend with it. -/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [CommRing R] (I : Ideal R)
  {M N P : ModuleCat.{v} R} (μ : M →ₗ[R] N →ₗ[R] P)

def pairing : (IdealQuotient.functor R I).obj M →ₗ[R] (IdealQuotient.functor R I).obj N →ₗ[R] (IdealQuotient.functor R I).obj P :=
  BilinearQuotient.lift₂ (I • ⊤ : Submodule R M) (I • ⊤ : Submodule R N)
    (μ.compr₂ (I • ⊤ : Submodule R P).mkQ)
    (fun _x hx y => (Submodule.Quotient.mk_eq_zero _).mpr
      (Submodule.smul_top_le_comap_smul_top I (μ.flip y) hx))
    (fun x _y hy => (Submodule.Quotient.mk_eq_zero _).mpr
      (Submodule.smul_top_le_comap_smul_top I (μ x) hy))

theorem pairing_mk (x : M) (y : N) :
    pairing I μ ((I • ⊤ : Submodule R M).mkQ x) ((I • ⊤ : Submodule R N).mkQ y) =
      (I • ⊤ : Submodule R P).mkQ (μ x y) := rfl

variable {M' N' P' : ModuleCat.{v} R} (ν : M' →ₗ[R] N' →ₗ[R] P')
  (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P')
  (hμ : ∀ x y, h (μ x y) = ν (f x) (g y))

include hμ in
theorem pairing_natural (x : (IdealQuotient.functor R I).obj M) (y : (IdealQuotient.functor R I).obj N) :
    (IdealQuotient.functor R I).map h (pairing I μ x y) =
      pairing I ν ((IdealQuotient.functor R I).map f x) ((IdealQuotient.functor R I).map g y) := by
  obtain ⟨x, rfl⟩ := (I • ⊤ : Submodule R M).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (I • ⊤ : Submodule R N).mkQ_surjective y
  exact congrArg (I • ⊤ : Submodule R P').mkQ (hμ x y)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotientProduct
