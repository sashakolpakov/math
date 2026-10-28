import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Interface
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.EstablishedArithmetic
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Action

/-! # Intrinsic -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Intrinsic.Construction

noncomputable section

/-! The actual TateComparison action on the very same PEL model as CentralAction.
Every field is a native construction, and every compatibility clause is
proved. Neither a TateComparison conclusion nor Construction/ElementaryDivisors is an assumption. The supplied
IntegralModel geometry and IsogenyQuotient one-step realization remain explicit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Action

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hgeometry : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)

def nativeTateComparisonAction : Interface.Construction.ActionData D where
  basis := TateComparison.CentralConvolution.sphericalBasis s q
  coeff := TateComparison.ConvolutionCoefficients.convolutionCoefficients s q (EstablishedArithmetic.Construction.provedElementaryDivisorsInput ℤ_[q] ℚ_[q])
  markingShift := D.qMarkingAutomorphism hgeometry hgood.2.2.1
  TAlb := D.heckeEnd hgeometry
  rho := D.rationalHeckeAction hgood hdegree hs hgeometry hIsogenyQuotient
    (EstablishedArithmetic.Construction.provedElementaryDivisorsInput ℤ_[q] ℚ_[q])
  rhoH1 := D.actualSphericalH1Action hgood hdegree hs hgeometry hIsogenyQuotient
    (EstablishedArithmetic.Construction.provedElementaryDivisorsInput ℤ_[q] ℚ_[q])

theorem nativeTateComparisonAction_spec :
    Interface.Construction.Conclusion D hgeometry hgood hIsogenyQuotient
      (nativeTateComparisonAction D hgeometry hgood hIsogenyQuotient hdegree hs) := by
  let hElementaryDivisors : TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q] := EstablishedArithmetic.Construction.provedElementaryDivisorsInput ℤ_[q] ℚ_[q]
  refine ⟨D.hasPolarizedFlagRealizations hgood hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors,
    TateComparison.CentralConvolution.sphericalBasis_isRaw s q, TateComparison.ConvolutionCoefficients.spherical_convolution s q hElementaryDivisors, ?_,
    D.centralIsMultiplicationByQ hgood hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors,
    D.isCentralGraph_qMarking hgood hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors, ?_,
    TateComparison.CentralConvolution.sphericalBasis_exists_integral_shift s q, ?_, ?_,
    D.heckeEnd_convolution hgood hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors,
    D.rationalHeckeAction_central_isUnit hgood hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors,
    D.actualSphericalH1Action_spec hgood hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors,
    D.heckeEnd_branchTrace hgeometry⟩
  · intro u v k _ _ b x
    exact D.neighbors_convolution hgood hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors u v b x
  · intro k _ _ b x
    exact D.central_neighbors_marking hgood hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors b x
  · intro t
    exact (D.rationalHeckeAction_basis hgood hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors t).symm
  · intro t k _ _ b j x y
    exact D.heckeEnd_point_push hgeometry t b j x y

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Intrinsic.Construction
