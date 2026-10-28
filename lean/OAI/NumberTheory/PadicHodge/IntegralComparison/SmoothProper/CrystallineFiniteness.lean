import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechInverseLimit
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechFiniteness
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Crystalline Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineFiniteness

noncomputable section

/-! Unconditional finite generation of original integral crystalline cohomology and finite dimensionality of its original rationalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (i : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechInverseLimit.compatible p k X i

include hprojective in
theorem integral_coefficient : Module.Finite R (Witt.Crystalline.integralCohomology p k X i) := by
  let : Module.Finite R L := CechFiniteness.cech_finite p k X hprojective i
  exact Module.Finite.equiv (CechInverseLimit.integralEquiv p k X hprojective i).symm

include hprojective in
theorem integral : Module.Finite (WittVector p k) (Witt.Crystalline.integralCohomology p k X i) := by
  let : Module.Finite R (Witt.Crystalline.integralCohomology p k X i) := integral_coefficient p k X hprojective i
  let e : Witt.Crystalline.integralCohomology p k X i →ₛₗ[(ULift.ringEquiv : R ≃+* WittVector p k).toRingHom]
      Witt.Crystalline.integralCohomology p k X i :=
    { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_surjective e Function.surjective_id

include hprojective in
theorem rational : Module.Finite (FractionRing (WittVector p k)) (Witt.Crystalline.rationalCohomology p k X i) := by
  let : Module.Finite (WittVector p k) (Witt.Crystalline.integralCohomology p k X i) := integral p k X hprojective i
  exact inferInstanceAs (Module.Finite (FractionRing (WittVector p k))
    (TensorProduct (WittVector p k) (FractionRing (WittVector p k)) (Witt.Crystalline.integralCohomology p k X i)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineFiniteness
