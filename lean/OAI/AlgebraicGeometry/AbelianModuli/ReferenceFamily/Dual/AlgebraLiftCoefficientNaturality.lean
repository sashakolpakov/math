import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AlgebraLiftCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftNaturality

/-! # Algebra Lift Coefficient Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AlgebraLiftCoefficientNaturality

noncomputable section

/-! The actual dual-number algebra map associated with a derivation
commutes with coefficient change. This retains the original map, as
needed when a single base tangent vector is evaluated on affine charts. -/

variable (k R C C' : Type) [CommRing k] [CommRing R] [CommRing C] [CommRing C']
    [Algebra k R] [Algebra k C] [Algebra k C'] [Algebra R C] [Algebra R C']
    [IsScalarTower k R C] [IsScalarTower k R C'] (q : C →ₐ[R] C')

theorem dualAlgebraLiftDerivationEquiv_symm_natural (d : Derivation k R C) :
    ((AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R C').symm (CoefficientLiftNaturality.coefficientDerivationMap k R C C' q d)).val =
      (NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)).comp ((AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R C).symm d).val := by
  let v := (AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R C).symm d
  let w := (AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R C').symm (CoefficientLiftNaturality.coefficientDerivationMap k R C C' q d)
  change w.val = (NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)).comp v.val
  apply AlgHom.ext
  intro r
  apply TrivSqZeroExt.ext
  · have hv : (v.val r).fst = algebraMap R C r := AlgHom.congr_fun v.property r
    have hw : (w.val r).fst = algebraMap R C' r := AlgHom.congr_fun w.property r
    change (w.val r).fst = q (v.val r).fst
    rw [hw, hv, q.commutes]
  · have hv : AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R C v = d :=
      (AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R C).apply_symm_apply d
    have hw : AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R C' w = CoefficientLiftNaturality.coefficientDerivationMap k R C C' q d :=
      (AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R C').apply_symm_apply _
    have hv' := Derivation.congr_fun hv r
    have hw' := Derivation.congr_fun hw r
    rw [AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv_apply] at hv' hw'
    change (w.val r).snd = q (v.val r).snd
    exact hw'.trans (congrArg q hv'.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AlgebraLiftCoefficientNaturality
