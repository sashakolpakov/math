import OAI.RepresentationTheory.Theta.Geometric.Affine.Tangents
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Point Cotangent -/

namespace OAI.RepresentationTheory.Theta.Geometric.PointCotangent

noncomputable section

/-! Point derivations are the dual of the actual cotangent fiber, with
arbitrary coefficient modules. This is the algebraic comparison needed
when the complex point is extended to a larger geometric field. -/

open scoped TensorProduct

variable (k A : Type) [Field k] [CommRing A] [Algebra k A]
  [Algebra A k]

abbrev pointCotangent := k ⊗[A] KaehlerDifferential k A

variable (V : Type) [AddCommGroup V] [Module k V] [Module A V]
  [IsScalarTower k A V] [IsScalarTower A k V]

def pointDerivationEquiv : Derivation k A V ≃ₗ[k] (pointCotangent k A →ₗ[k] V) :=
  ((KaehlerDifferential.linearMapEquivDerivation k A).symm.restrictScalars k).trans
    (LinearMap.liftBaseChangeEquiv k)

theorem pointDerivationEquiv_D (δ : Derivation k A V) (a : A) :
    pointDerivationEquiv k A V δ (1 ⊗ₜ[A] KaehlerDifferential.D k A a) = δ a := by
  change δ.liftKaehlerDifferential.liftBaseChange k (1 ⊗ₜ[A] KaehlerDifferential.D k A a) = _
  rw [LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]

variable {V}

theorem pointCotangent_linearMap_ext (f g : pointCotangent k A →ₗ[k] V)
    (h : ∀ a : A, f (1 ⊗ₜ[A] KaehlerDifferential.D k A a) =
      g (1 ⊗ₜ[A] KaehlerDifferential.D k A a)) : f = g := by
  apply (pointDerivationEquiv k A V).symm.injective
  apply Derivation.ext
  intro a
  have hf := pointDerivationEquiv_D k A V ((pointDerivationEquiv k A V).symm f) a
  have hg := pointDerivationEquiv_D k A V ((pointDerivationEquiv k A V).symm g) a
  rw [LinearEquiv.apply_symm_apply] at hf hg
  exact hf.symm.trans ((h a).trans hg)

variable {W : Type} [AddCommGroup W] [Module k W] [Module A W]
  [IsScalarTower k A W] [IsScalarTower A k W]

theorem pointDerivationEquiv_coefficients (f : V →ₗ[k] W) (δ : Derivation k A V) :
    pointDerivationEquiv k A W (δ.llcomp (f.restrictScalars A)) =
      f.comp (pointDerivationEquiv k A V δ) := by
  apply pointCotangent_linearMap_ext k A
  intro a
  rw [pointDerivationEquiv_D, LinearMap.comp_apply, pointDerivationEquiv_D]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric.PointCotangent
