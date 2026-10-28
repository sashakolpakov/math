import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechInverseLimit
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechScalarSystem

/-! # Crystalline Degree Zero Torsion -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineDegreeZeroTorsion

noncomputable section

/-! Multiplication by p is injective on the original integral crystalline degree-zero cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

theorem inclusion_injective (n : ℕ) :
    Function.Injective (CechScalarSystem.inclusion p k X n 0) := by
  let := ShortExactHomologyKernel.mono_zero
    (WittCechExactSequence.sequence p k X n)
    (WittCechExactSequence.shortExact p k X n)
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

theorem compatible_zero (x : CechInverseLimit.compatible p k X 0)
    (hx : (p : R) • x = 0) : x = 0 := by
  have hc := (CechInverseLimit.mem_compatible p k X 0 x.val).mp x.property
  apply Subtype.ext
  funext n
  apply inclusion_injective p k X n
  have hz : (p : R) • x.val (n + 1) = 0 := congrArg (fun z => z.val (n + 1)) hx
  exact (congrArg (CechScalarSystem.inclusion p k X n 0) (hc n).symm).trans
    ((CechScalarSystem.inclusion_map p k X n 0 (x.val (n + 1))).trans
      (hz.trans (CechScalarSystem.inclusion p k X n 0).map_zero.symm))

theorem integral_zero (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)
    (x : Witt.Crystalline.integralCohomology p k X 0) (hx : (p : WittVector p k) • x = 0) : x = 0 := by
  let e : Witt.Crystalline.integralCohomology p k X 0 ≃ₗ[R]
      CechInverseLimit.compatible p k X 0 :=
    CechInverseLimit.integralEquiv p k X hprojective 0
  apply e.injective
  have hx' : (ULift.up (p : WittVector p k) : R) • x = 0 := hx
  have hp : (p : R) • e x = 0 :=
    (e.map_smul (ULift.up (p : WittVector p k) : R) x).symm.trans
      ((congrArg e hx').trans e.map_zero)
  exact (compatible_zero p k X (e x) hp).trans e.map_zero.symm

theorem regular (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) :
    IsSMulRegular (Witt.Crystalline.integralCohomology p k X 0) (p : WittVector p k) := by
  intro x y h
  apply sub_eq_zero.mp
  apply integral_zero p k X hprojective
  rw [smul_sub]
  exact sub_eq_zero.mpr h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineDegreeZeroTorsion
