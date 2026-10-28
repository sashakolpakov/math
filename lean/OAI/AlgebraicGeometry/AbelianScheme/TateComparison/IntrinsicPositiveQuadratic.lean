import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TypeElevenBilinear
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.PeriodBilinearExt
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps

/-! # Intrinsic Positive Quadratic -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPositiveQuadratic

noncomputable section

/-! The actual ample Chern covector defines a continuous positive
quadratic function, preserved by every period-pairing isometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)

local instance : IsIntegral A.toOver.left := A.variety.property
local instance : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance : NormedSpace ℝ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) := inferInstanceAs (NormedSpace ℝ A.variety.analyticModel)

theorem covectorQuadratic_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]
    (c : V [⋀^Fin 2]→L[ℝ] ℂ) (a : ℝ) (u : V) :
    (c ![a • u, Complex.I • (a • u)]).re = a ^ 2 * (c ![u, Complex.I • u]).re := by
  rw [← AbelianModuli.ReferenceFamily.TypeElevenBilinear.realCovectorBilinear_apply, ← AbelianModuli.ReferenceFamily.TypeElevenBilinear.realCovectorBilinear_apply, smul_comm Complex.I a]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

def nativeChernQuadratic (u : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) : ℝ :=
  (AbelianModuli.ReferenceFamily.AmpleChernInvariant.nativeChernCovector A L ![u, Complex.I • u]).re

theorem nativeChernQuadratic_continuous : Continuous (nativeChernQuadratic A L) := by
  have hv : Continuous (fun u : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A => ![u, Complex.I • u]) := by fun_prop
  exact Complex.continuous_re.comp ((AbelianModuli.ReferenceFamily.AmpleChernInvariant.nativeChernCovector A L).cont.comp hv)

theorem nativeChernQuadratic_smul (a : ℝ) (u : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    nativeChernQuadratic A L (a • u) = a ^ 2 * nativeChernQuadratic A L u :=
  covectorQuadratic_smul (AbelianModuli.ReferenceFamily.AmpleChernInvariant.nativeChernCovector A L) a u

theorem nativeChernQuadratic_positive (hL : L.IsAmple) (u : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (hu : u ≠ 0) :
    0 < nativeChernQuadratic A L u := AbelianModuli.ReferenceFamily.AmpleChernInvariant.nativeChernCovector_positive_model A L hL u hu

theorem nativeChernCovector_isometry (f : A.toOver ⟶ A.toOver) [IsMonHom f]
    (hf : ∀ x y : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A,
      AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) = AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L x y)
    (u v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    AbelianModuli.ReferenceFamily.AmpleChernInvariant.nativeChernCovector A L ![AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift f u, AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift f v] = AbelianModuli.ReferenceFamily.AmpleChernInvariant.nativeChernCovector A L ![u, v] := by
  let B := AbelianModuli.ReferenceFamily.TypeElevenBilinear.covectorBilinear (V := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (AbelianModuli.ReferenceFamily.AmpleChernInvariant.nativeChernCovector A L)
  let F := (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift f).restrictScalars ℝ
  have he : B.compl₁₂ F F = B := by
    apply AbelianModuli.ReferenceFamily.Real.PeriodBilinearExt.realPeriodBilinear_ext A
    intro x y
    change AbelianModuli.ReferenceFamily.TypeElevenBilinear.covectorBilinear (V := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (AbelianModuli.ReferenceFamily.AmpleChernInvariant.nativeChernCovector A L)
      (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift f x.val) (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift f y.val) =
        AbelianModuli.ReferenceFamily.TypeElevenBilinear.covectorBilinear (V := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (AbelianModuli.ReferenceFamily.AmpleChernInvariant.nativeChernCovector A L) x.val y.val
    exact (AbelianModuli.ReferenceFamily.TypeElevenBilinear.covectorBilinear_apply (V := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) _ _ _).trans
      ((AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod.nativeChernForm_covector A L (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y)).trans
        ((congrArg (fun z : ℚ => (z : ℂ)) (hf x y)).trans
          ((AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod.nativeChernForm_covector A L x y).symm.trans
            (AbelianModuli.ReferenceFamily.TypeElevenBilinear.covectorBilinear_apply (V := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) _ _ _).symm)))
  exact (AbelianModuli.ReferenceFamily.TypeElevenBilinear.covectorBilinear_apply _ _ _).symm.trans
    ((LinearMap.congr_fun₂ he u v).trans (AbelianModuli.ReferenceFamily.TypeElevenBilinear.covectorBilinear_apply _ _ _))

theorem nativeChernQuadratic_isometry (f : A.toOver ⟶ A.toOver) [IsMonHom f]
    (hf : ∀ x y : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A,
      AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) = AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L x y)
    (u : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) : nativeChernQuadratic A L (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift f u) = nativeChernQuadratic A L u := by
  unfold nativeChernQuadratic
  rw [← (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift f).map_smul Complex.I u, nativeChernCovector_isometry A L f hf]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPositiveQuadratic
