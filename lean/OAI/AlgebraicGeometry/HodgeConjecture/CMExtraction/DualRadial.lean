import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RadialSatake
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ContragredientRadial
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphism
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Opposition
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualSatakeParameters

/-! # Dual Radial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadial.Iwasawa

noncomputable section

/-! The native inverse-transpose convention is evaluated through the same
normalized Satake transform at (sqrt(q), sqrt(q) inverse, e inverse). -/

open scoped Classical TensorProduct

variable (q : ℕ) [Fact q.Prime]

def dualRadialSatakeCharacter (e : ℂˣ) : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] ℂ :=
  (SatakeKernel.Iwasawa.evaluateLattice ((Units.coeHom ℂ).comp (SatakeParameters.Iwasawa.torusCharacter (DualSatakeParameters.Iwasawa.dualRadialTorusPoint q e)))).comp
    (RadialSatake.Iwasawa.normalizedSatake q)

theorem dualRadialSatakeCharacter_rational (e : ℂˣ) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    dualRadialSatakeCharacter q e ((1 : ℂ) ⊗ₜ[ℚ] T) =
      (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T).sum
        (fun x a => (a : ℂ) * (e.val / Radial.Cyclicity.normalization q) ^ (-((Borel.Iwasawa.decomposition q).height x 2))) := by
  unfold dualRadialSatakeCharacter RadialSatake.Iwasawa.normalizedSatake
  rw [AlgHom.comp_apply, AlgHom.comp_apply, HeckeScalarExtension.Iwasawa.complexHecke_tmul, one_smul]
  change SatakeKernel.Iwasawa.evaluateLattice _ (RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.twist _
    ((Borel.Iwasawa.decomposition q).constantTerm (HeckeScalarExtension.Iwasawa.rationalComplexHecke _ T))) = _
  rw [SatakeKernel.Iwasawa.evaluate_twist, SatakeKernel.Iwasawa.evaluate_constantTerm_rational]
  unfold Finsupp.sum
  apply Finset.sum_congr rfl
  intro x _
  apply congrArg (fun z : ℂ => (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T x : ℂ) * z)
  have h := congrArg (fun u : ℂˣ => (u : ℂ))
    (DualSatakeParameters.Iwasawa.dualRadialTorusPoint_weight q e ((Borel.Iwasawa.decomposition q).height x) (Borel.Iwasawa.height_sum q x))
  simpa only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.coeHom_apply,
    Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_div_eq_div_val,
    Units.val_pow_eq_pow_val, SatakeParameters.Iwasawa.normalization_eq_sqrt_cube] using h

theorem radialCharacter_contragredient_rational
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (e : ℂ) (he : e ≠ 0)
    (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    Radial.Characters.radialCharacter q hElementaryDivisors e he ((1 : ℂ) ⊗ₜ[ℚ] HeckeAutomorphismAction.Local.contragredientHecke q T) =
      dualRadialSatakeCharacter q (Units.mk0 e he) ((1 : ℂ) ⊗ₜ[ℚ] T) := by
  change Radial.Characters.radialEigenvalue q hElementaryDivisors e _ = _
  rw [Radial.ConstantTerm.Iwasawa.radialEigenvalue_kernel, dualRadialSatakeCharacter_rational]
  have heq : HeckeAutomorphismAction.Local.contragredientHecke q T =
      HeckeAutomorphism.Local.heckeAutomorphism (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Opposition.Iwasawa.opposition q) (Opposition.Iwasawa.opposition_integral_iff q) T :=
    (Opposition.Iwasawa.opposition_hecke q T).symm
  rw [heq, HeckeAutomorphism.Local.heckeAutomorphism_kernel_sum]
  unfold Finsupp.sum
  apply Finset.sum_congr rfl
  intro x _
  dsimp only
  rw [Opposition.Iwasawa.opposition_height]
  rfl

theorem radialCharacter_contragredient_eq_satake
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (e : ℂ) (he : e ≠ 0) :
    (Radial.Characters.radialCharacter q hElementaryDivisors e he).comp (ContragredientRadial.Local.contragredientComplexHecke q).toAlgHom =
      dualRadialSatakeCharacter q (Units.mk0 e he) := by
  have hbase (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
      ((Radial.Characters.radialCharacter q hElementaryDivisors e he).comp (ContragredientRadial.Local.contragredientComplexHecke q).toAlgHom)
          ((1 : ℂ) ⊗ₜ[ℚ] T) =
        dualRadialSatakeCharacter q (Units.mk0 e he) ((1 : ℂ) ⊗ₜ[ℚ] T) :=
    radialCharacter_contragredient_rational q hElementaryDivisors e he T
  apply AlgHom.ext
  intro T
  induction T using TensorProduct.inductionOn with
  | add T U hT hU => simp only [map_add, hT, hU]
  | tmul c T =>
      have ht : c ⊗ₜ[ℚ] T = c • ((1 : ℂ) ⊗ₜ[ℚ] T) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, map_smul, map_smul, hbase]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadial.Iwasawa
