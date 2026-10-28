import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.PeriodBilinearExt
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Real Period Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RealPeriodMaps.IntrinsicRationalPeriods

noncomputable section

/-! Every rational map on the actual native period span has a unique
real-linear extension to the native tangent space. Rational isomorphisms
extend to continuous real-linear isomorphisms, without requiring them
to preserve the original complex structure. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

local instance realPeriodIntegral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.IsIntegral A.toOver.left :=
  A.variety.property
local instance realPeriodFull (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :=
  HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full Torsion.IntrinsicTorsion.e06Input A

theorem rationalPeriodBasis_real (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (i : Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom)) :
    (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i).val = RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i :=
  (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis_coe A i).trans
    (Module.Basis.ofZLatticeBasis_apply ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (Torsion.IntrinsicTorsion.periodBasis A) i).symm

variable {A B C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}

def nativeRealPeriodMap (f : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B) :
    HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B :=
  (RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).constr ℝ (fun i => (f (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i)).val)

theorem nativeRealPeriodMap_rational (f : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B)
    (x : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) : nativeRealPeriodMap f x.val = (f x).val := by
  have h : ((nativeRealPeriodMap f).restrictScalars ℚ).comp (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A).subtype =
      (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B).subtype.comp f := by
    apply (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A).ext
    intro i
    change nativeRealPeriodMap f (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i).val = (f (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i)).val
    rw [rationalPeriodBasis_real, nativeRealPeriodMap, Module.Basis.constr_basis]
  exact LinearMap.congr_fun h x

theorem nativeRealPeriodMap_ext (F G : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
    (h : ∀ x : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A, F x.val = G x.val) : F = G := by
  apply (RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).ext
  intro i
  rw [← rationalPeriodBasis_real]
  exact h (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i)

theorem nativeRealPeriodMap_id :
    nativeRealPeriodMap (LinearMap.id : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) = LinearMap.id := by
  apply nativeRealPeriodMap_ext
  intro x
  exact nativeRealPeriodMap_rational LinearMap.id x

theorem nativeRealPeriodMap_comp
    (f : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B)
    (h : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B →ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods C) :
    nativeRealPeriodMap (h.comp f) = (nativeRealPeriodMap h).comp (nativeRealPeriodMap f) := by
  apply nativeRealPeriodMap_ext
  intro x
  change nativeRealPeriodMap (h.comp f) x.val = nativeRealPeriodMap h (nativeRealPeriodMap f x.val)
  rw [nativeRealPeriodMap_rational, nativeRealPeriodMap_rational, nativeRealPeriodMap_rational]
  rfl

def nativeRealPeriodIso (u : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B) :
    HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B :=
  LinearEquiv.ofLinearMap (nativeRealPeriodMap u.toLinearMap) (nativeRealPeriodMap u.symm.toLinearMap)
    (by
      apply nativeRealPeriodMap_ext
      intro x
      change nativeRealPeriodMap u.toLinearMap (nativeRealPeriodMap u.symm.toLinearMap x.val) = x.val
      rw [nativeRealPeriodMap_rational, nativeRealPeriodMap_rational]
      exact congrArg Subtype.val (u.apply_symm_apply x))
    (by
      apply nativeRealPeriodMap_ext
      intro x
      change nativeRealPeriodMap u.symm.toLinearMap (nativeRealPeriodMap u.toLinearMap x.val) = x.val
      rw [nativeRealPeriodMap_rational, nativeRealPeriodMap_rational]
      exact congrArg Subtype.val (u.symm_apply_apply x))

theorem nativeRealPeriodIso_rational (u : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B)
    (x : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) : nativeRealPeriodIso u x.val = (u x).val :=
  nativeRealPeriodMap_rational u.toLinearMap x

def nativeRealPeriodContinuousIso (u : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B) :
    HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃L[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B :=
  (nativeRealPeriodIso u).toContinuousLinearEquiv

theorem nativeRealPeriodMap_preserves_form
    (u : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B)
    (F : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℝ] ℝ)
    (G : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B →ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B →ₗ[ℝ] ℝ)
    (hu : ∀ x y : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A, G (u x).val (u y).val = F x.val y.val) :
    G.compl₁₂ (nativeRealPeriodMap u) (nativeRealPeriodMap u) = F := by
  apply Real.PeriodBilinearExt.realPeriodBilinear_ext A
  intro x y
  change G (nativeRealPeriodMap u x.val) (nativeRealPeriodMap u y.val) = F x.val y.val
  rw [nativeRealPeriodMap_rational, nativeRealPeriodMap_rational]
  exact hu x y

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RealPeriodMaps.IntrinsicRationalPeriods
