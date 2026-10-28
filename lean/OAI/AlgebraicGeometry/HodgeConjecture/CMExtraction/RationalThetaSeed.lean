import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PreprimeCalibration
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ReferenceFrame
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralOpen

/-! # Rational Theta Seed -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalThetaSeed.Intrinsic

noncomputable section

/-! A rational source datum for the native construction. Its source
away group is the rational unitary group with the discrete topology and
the literal marked lattice subgroup. The native construction subsequently
supplies the actual finite away group, topology, and product splitting. -/

open scoped Classical _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ReferenceFrame.ParameterChoices

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (B : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : B.HasIntegralModelGeometry)
  (hμ : B.reference.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : PreprimeCalibration.Intrinsic.RetainedPreprimeData E B.reference hg.reference_admissible hμ v hv W)
  [TopologicalSpace (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.reference.b)]
  [DiscreteTopology (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.reference.b)]

def rationalThetaSeedInitial :
    RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.reference.b) MpR MpF MpA where
  pel := B
  localEmbedding := LocalEmbedding.ParameterChoices.nativeFieldEmbedding B
  away := MonoidHom.id _
  localLevel := ⟨IntegralOpen.Intrinsic.integralSL3Open q, rfl⟩
  awayLevel := ⊤
  weil := W
  splitting := (Intrinsic.RationalSplitting.nativeRationalFiniteSplitting E B.reference hg.reference_admissible
    hμ v hv R.coordinates R.pairing W).comp (MonoidHom.snd _ _)
  period := Intrinsic.ThetaCoordinates.Multiplicity.nativeThetaPeriod E B.reference hg.reference_admissible hμ v hv R.coordinates R.pairing
  project := Intrinsic.CotangentTheta.Multiplicity.nativeCotangentProjection E B.reference hg.reference_admissible
    hμ v hv R.coordinates R.pairing

def rationalThetaSeedLevel : Subgroup (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.reference.b) :=
  let D := rationalThetaSeedInitial E B hg hμ v hv W R
  D.rationalAwayLevel ⊓ ⨅ w : Fin s × Bool, ⨅ (_ : w.1 ≠ B.reference.distinguished),
    (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).comap (D.localMatrix w)

def rationalThetaSeed :
    RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.reference.b) MpR MpF MpA :=
  { rationalThetaSeedInitial E B hg hμ v hv W R with
    awayLevel := {
      toSubgroup := rationalThetaSeedLevel E B hg hμ v hv W R
      isOpen' := isOpen_discrete _ } }

theorem rationalThetaSeed_finiteCoordinates
    (hframe : Intrinsic.ReferenceFrame.ParameterChoices.referenceFrameBound E B.reference hg.reference_admissible < q) :
    (rationalThetaSeed E B hg hμ v hv W R).HasFiniteCoordinates := by
  refine ⟨LocalEmbedding.ParameterChoices.nativeFieldEmbedding_onIntegers B, ?_, ?_⟩
  · intro w
    exact Intrinsic.ReferenceFrame.ParameterChoices.native_reference_frame_standard E B hg hframe w
  · intro γ
    change γ ∈ rationalThetaSeedLevel E B hg hμ v hv W R ↔ _
    constructor
    · intro h
      exact ⟨h.1, fun w hw => Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp h.2 w) hw⟩
    · rintro ⟨ha, hl⟩
      exact ⟨ha, Subgroup.mem_iInf.mpr (fun w => Subgroup.mem_iInf.mpr (fun hw => hl w hw))⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalThetaSeed.Intrinsic
