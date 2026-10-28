import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData

/-! # Isogeny Lie Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IsogenyLieBaseChange.Construction

noncomputable section

/-! The original kernel bound and coefficient-intertwining equation
are preserved on every actual base change of the isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S S' : Scheme.{u}} {g h : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (s : S' ⟶ S) (m : ℕ)

theorem isogenyKernelBound_baseChange
    (hf : ∀ (T : Over S) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ m = 1)
    (T : Over S') (x : T ⟶ (A.pullback s).scheme) (hx : x ≫ (f.pullback s).hom = 1) :
    x ^ m = 1 := by
  let x0 := f.kernelBaseChangeEquiv s T ⟨x, hx⟩
  have h0 : x0.val ^ m = 1 := hf ((Over.map s).obj T) x0.val x0.property
  apply (A.baseChangePointsMulEquiv s T).injective
  rw [map_pow, map_one]
  exact h0

variable {O : Type u} [CommRing O]
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O B)

theorem isogenyAction_intertwines_baseChange
    (hc : ∀ a, ρ.map a ≫ f.hom = f.hom ≫ σ.map a) (a : O) :
    (ρ.pullback s).map a ≫ (f.pullback s).hom =
      (f.pullback s).hom ≫ (σ.pullback s).map a := by
  exact ((Over.pullback s).map_comp (ρ.map a) f.hom).symm.trans
    ((congrArg ((Over.pullback s).map) (hc a)).trans ((Over.pullback s).map_comp f.hom (σ.map a)))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IsogenyLieBaseChange.Construction
