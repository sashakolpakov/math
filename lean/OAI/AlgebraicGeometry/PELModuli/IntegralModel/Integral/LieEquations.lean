import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieEigenspaces
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.Actions

/-! # Lie Equations -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieEquations

noncomputable section

/-! The actual integral Lie eigenspace is the kernel of one finite
linear map, using the integral basis of the CM order in every characteristic. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace AlgebraicLie

theorem additive_eq_of_integral_basis
    {E M : Type} [Field E] [NumberField E] [AddCommGroup M]
    (f q : NumberField.RingOfIntegers E → M)
    (hf0 : f 0 = 0) (hq0 : q 0 = 0)
    (hfadd : ∀ a b, f (a + b) = f a + f b)
    (hqadd : ∀ a b, q (a + b) = q a + q b)
    (h : ∀ i, f (Finite.Actions.integralActionBasis E i) = q (Finite.Actions.integralActionBasis E i)) : f = q := by
  let F : NumberField.RingOfIntegers E →+ M :=
    { toFun := f, map_zero' := hf0, map_add' := hfadd }
  let Q : NumberField.RingOfIntegers E →+ M :=
    { toFun := q, map_zero' := hq0, map_add' := hqadd }
  have he : F.toIntLinearMap = Q.toIntLinearMap := (Finite.Actions.integralActionBasis E).ext h
  exact funext (LinearMap.congr_fun he)

variable {E k : Type} [Field E] [NumberField E] [Field k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (τ : NumberField.RingOfIntegers E →+* k)

theorem mem_eigenspace_iff_basis (v : LiePoints.AlgebraicLie.Space A.scheme) :
    v ∈ LieEigenspaces.AlgebraicLie.eigenspace A ρ τ ↔
      ∀ i : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E)),
        LieAlgebraic.AlgebraicLie.action A ρ (Finite.Actions.integralActionBasis E i) v = τ (Finite.Actions.integralActionBasis E i) • v := by
  rw [LieEigenspaces.AlgebraicLie.mem_eigenspace_iff]
  constructor
  · exact fun h i => h (Finite.Actions.integralActionBasis E i)
  · intro h
    have he := additive_eq_of_integral_basis (fun a => LieAlgebraic.AlgebraicLie.action A ρ a v) (fun a => τ a • v)
      (by rw [LieAlgebraic.AlgebraicLie.action_apply, LieAlgebraic.AlgebraicLie.action_zero]; rfl) (by rw [map_zero, zero_smul])
      (fun a b => by rw [LieAlgebraic.AlgebraicLie.action_apply, LieAlgebraic.AlgebraicLie.action_add, LieAlgebraic.AlgebraicLie.action_apply, LieAlgebraic.AlgebraicLie.action_apply]; rfl)
      (fun a b => by rw [map_add, add_smul]) h
    intro a
    exact congrFun he a

def integralEigenEquations : LiePoints.AlgebraicLie.Space A.scheme →ₗ[k]
    (Fin (Module.finrank ℤ (NumberField.RingOfIntegers E)) → LiePoints.AlgebraicLie.Space A.scheme) :=
  LinearMap.pi fun i => LieAlgebraic.AlgebraicLie.action A ρ (Finite.Actions.integralActionBasis E i) -
    τ (Finite.Actions.integralActionBasis E i) • LinearMap.id

theorem eigenspace_eq_kernel : LieEigenspaces.AlgebraicLie.eigenspace A ρ τ = LinearMap.ker (integralEigenEquations A ρ τ) := by
  ext v
  rw [mem_eigenspace_iff_basis, LinearMap.mem_ker]
  change (∀ i, LieAlgebraic.AlgebraicLie.action A ρ (Finite.Actions.integralActionBasis E i) v = τ (Finite.Actions.integralActionBasis E i) • v) ↔
    (fun i => LieAlgebraic.AlgebraicLie.action A ρ (Finite.Actions.integralActionBasis E i) v - τ (Finite.Actions.integralActionBasis E i) • v) = 0
  simp only [funext_iff, Pi.zero_apply, sub_eq_zero]

end AlgebraicLie

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieEquations
