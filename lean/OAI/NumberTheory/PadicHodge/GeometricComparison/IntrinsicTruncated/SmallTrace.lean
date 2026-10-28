import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.Connected
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.TopEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveCover

/-! # Small Trace -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.SmallTrace.AbelianModel

noncomputable section

/-! The actual normalized top-form trace in the affine-cover
coordinates used by the bounded crystalline comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def transportTrace {M N R : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup R]
    (τ : {f : N →+ R // Function.Bijective f}) (e : M ≃+ N) :
    {f : M →+ R // Function.Bijective f} :=
  ⟨τ.val.comp e.toAddMonoidHom, τ.property.comp e.bijective⟩

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedTopFormCoverIso (n : ℕ) (hpos : 0 < A.dimension) :
    A.TruncatedSmallTopForms n ≃+ A.TruncatedTopFormCohomology n := by
  letI : (Integral.FormsModules.IntegralFormsModules.sheaf (TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedModel n).scheme A.dimension).IsQuasicoherent :=
    IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent (TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedModel n).scheme A.dimension
  exact (IntegralComparison.ModuleCech.PositiveCover.Comparison.iso (TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedModel n).scheme (A.truncatedSmallCover n) (A.truncatedTraceCover n)
    (A.truncatedSmallCover_top n) (A.truncatedTraceCover_top n)
    (A.truncatedSmallCover_affine n) (A.truncatedTraceCover_affine n)
    (Integral.FormsModules.IntegralFormsModules.sheaf (TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedModel n).scheme A.dimension) A.dimension hpos).addCommGroupIsoToAddEquiv

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedSmallTopFormTraceData (n : ℕ) (hpos : 0 < A.dimension) :
    {τ : A.TruncatedSmallTopForms n →+
      IntegralComparison.Projective.TopTracePairing.coefficientRing (TruncatedModel.NativeTruncatedBase.Ring q n) //
        Function.Bijective τ} :=
  transportTrace (A.truncatedTopFormTraceData n) (A.truncatedTopFormCoverIso n hpos)

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedSmallTopFormTrace (n : ℕ) (hpos : 0 < A.dimension) :
    A.TruncatedSmallTopForms n →+
      IntegralComparison.Projective.TopTracePairing.coefficientRing (TruncatedModel.NativeTruncatedBase.Ring q n) :=
  (A.truncatedSmallTopFormTraceData n hpos).val

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedSmallTopFormTrace_bijective (n : ℕ) (hpos : 0 < A.dimension) :
    Function.Bijective (A.truncatedSmallTopFormTrace n hpos) :=
  (A.truncatedSmallTopFormTraceData n hpos).property

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.SmallTrace.AbelianModel
