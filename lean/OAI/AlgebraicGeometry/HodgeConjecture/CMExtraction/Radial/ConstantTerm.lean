import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BorelRadial
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.ShellCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Characters
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeScalarExtension

/-! # Constant Term -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.ConstantTerm.Iwasawa

noncomputable section

/-! The actual spherical image of the unit ball is the finite sum of
balls indexed by Iwasawa height, with the original Hecke coefficients. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime]

theorem coset_ball_sphere (x : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (n : ℤ) :
    Hecke.matrixSubstitution q x.out (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0) (Hecke.spherePoint q n) =
      RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q ((Borel.Iwasawa.decomposition q).height x 0) (Hecke.spherePoint q n) := by
  let b := (Borel.Iwasawa.decomposition q).representative x
  have h := RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weil_value_eq_of_same_coset
    (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Hecke.matrixSubstitution q)
    (Hecke.radialFixedEmbedding q (Cyclicity.ball q 0))
    ((QuotientGroup.out_eq' x).trans ((Borel.Iwasawa.decomposition q).representative_spec x).symm)
  have he := congrArg (fun f : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ => f (Hecke.spherePoint q n)) h
  change Hecke.matrixSubstitution q x.out (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0) (Hecke.spherePoint q n) =
    Hecke.matrixSubstitution q b.val (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0) (Hecke.spherePoint q n) at he
  exact he.trans (BorelRadial.Iwasawa.borel_ball_sphere q b n)

theorem spherical_unit_ball (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    Action.sphericalRadialAction q T (Cyclicity.ball q 0) =
      (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T).sum
        (fun x a => (a : ℂ) • Cyclicity.ball q ((Borel.Iwasawa.decomposition q).height x 0)) := by
  apply ShellCoordinates.radial_ext_sphere q
  intro n
  change Hecke.sphericalFunctionAction q T (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0) (Hecke.spherePoint q n) = _
  simp only [Hecke.sphericalFunctionAction, RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    Pi.smul_apply, Finset.sum_apply, Submodule.coe_sum, Submodule.coe_smul,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [coset_ball_sphere]
  rfl

theorem radialEigenvalue_kernel
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (e : ℂ)
    (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    Characters.radialEigenvalue q hElementaryDivisors e ((1 : ℂ) ⊗ₜ[ℚ] T) =
      (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T).sum
        (fun x a => (a : ℂ) * (e / Cyclicity.normalization q) ^ ((Borel.Iwasawa.decomposition q).height x 0)) := by
  unfold Characters.radialEigenvalue
  rw [Algebra.sphericalRadialComplexAlgebra_tmul]
  simp only [one_smul]
  rw [spherical_unit_ball]
  simp only [Finsupp.sum, map_sum, map_smul, Characters.dilationFunctional_ball, smul_eq_mul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.ConstantTerm.Iwasawa
