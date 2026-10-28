import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Kernel Graph Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.KernelGraphCoordinates

noncomputable section

/-! The free-coordinate projection identifies a Jacobian kernel with
the free tangent coordinates whenever its selected block is invertible. -/

variable {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def kernelFreeProjection (F : (U × V) →ₗ[K] W) : F.ker →ₗ[K] U :=
  (LinearMap.fst K U V).comp F.ker.subtype

theorem kernelFreeProjection_bijective (F : (U × V) →ₗ[K] W)
    (e : V ≃ₗ[K] W) (he : ∀ v, F (0, v) = e v) :
    Function.Bijective (kernelFreeProjection F) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply Prod.ext
    · exact h
    · have hd : F (0, x.val.2 - y.val.2) = 0 := by
        have hz : (0, x.val.2 - y.val.2) = x.val - y.val := by
          apply Prod.ext
          · exact (sub_eq_zero.mpr h).symm
          · rfl
        rw [hz, map_sub, x.property, y.property, sub_self]
      rw [he] at hd
      exact sub_eq_zero.mp (e.injective (hd.trans e.map_zero.symm))
  · intro u
    let v := -e.symm (F (u, 0))
    have hv : F (u, v) = 0 := by
      have hz : (u, v) = (u, 0) + (0, v) := by simp
      rw [hz, map_add, he]
      dsimp only [v]
      rw [map_neg, e.apply_symm_apply, add_neg_cancel]
    exact ⟨⟨(u, v), hv⟩, rfl⟩

def kernelFreeEquiv (F : (U × V) →ₗ[K] W)
    (e : V ≃ₗ[K] W) (he : ∀ v, F (0, v) = e v) : F.ker ≃ₗ[K] U :=
  LinearEquiv.ofBijective (kernelFreeProjection F) (kernelFreeProjection_bijective F e he)

theorem kernelFreeEquiv_inverse_characterization (F : (U × V) →ₗ[K] W)
    (e : V ≃ₗ[K] W) (he : ∀ v, F (0, v) = e v)
    (u : U) (w : U × V) (hw : F w = 0) (hfirst : w.1 = u) :
    (kernelFreeEquiv F e he).symm u = ⟨w, hw⟩ := by
  apply (kernelFreeEquiv F e he).injective
  exact ((kernelFreeEquiv F e he).apply_symm_apply u).trans hfirst.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.KernelGraphCoordinates
