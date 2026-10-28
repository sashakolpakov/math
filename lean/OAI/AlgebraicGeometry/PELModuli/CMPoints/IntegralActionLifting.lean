import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.Actions

/-! # Integral Action Lifting -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralActionLifting

noncomputable section

/-! An integral ring action lifts through an injective ring map once
the images of one finite integral basis lift. All multiplication and
unit identities are proved by reflection. -/

open _root_.Module

def ringActionLiftOfBasis
    {O R S : Type*} [Ring O] [Ring R] [Ring S] {I : Type*}
    (b : Basis I ℤ O) (φ : R →+* S) (hφ : Function.Injective φ)
    (ρ : O →+* S) (v : I → R) (hv : ∀ i, φ (v i) = ρ (b i)) : O →+* R := by
  have hmap : ∀ x, φ (IntegralModel.Finite.Actions.basisExtension b v x) = ρ x := by
    have he : φ.toAddMonoidHom.toIntLinearMap.comp (IntegralModel.Finite.Actions.basisExtension b v) =
        ρ.toAddMonoidHom.toIntLinearMap := b.ext (fun i => by
      change φ (IntegralModel.Finite.Actions.basisExtension b v (b i)) = ρ (b i)
      rw [IntegralModel.Finite.Actions.basisExtension_basis]
      exact hv i)
    exact fun x => LinearMap.congr_fun he x
  apply IntegralModel.Finite.Actions.ringHomOfBasis b v
  · apply hφ
    rw [hmap, map_one, map_one]
  · intro i j
    apply hφ
    rw [hmap, map_mul, map_mul, hv, hv]

theorem ringActionLiftOfBasis_comparison
    {O R S : Type*} [Ring O] [Ring R] [Ring S] {I : Type*}
    (b : Basis I ℤ O) (φ : R →+* S) (hφ : Function.Injective φ)
    (ρ : O →+* S) (v : I → R) (hv : ∀ i, φ (v i) = ρ (b i)) :
    φ.comp (ringActionLiftOfBasis b φ hφ ρ v hv) = ρ := by
  apply RingHom.ext
  intro x
  have he : (φ.comp (ringActionLiftOfBasis b φ hφ ρ v hv)).toAddMonoidHom.toIntLinearMap =
      ρ.toAddMonoidHom.toIntLinearMap := b.ext (fun i => by
    change φ (IntegralModel.Finite.Actions.basisExtension b v (b i)) = ρ (b i)
    rw [IntegralModel.Finite.Actions.basisExtension_basis, hv])
  exact LinearMap.congr_fun he x

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralActionLifting
