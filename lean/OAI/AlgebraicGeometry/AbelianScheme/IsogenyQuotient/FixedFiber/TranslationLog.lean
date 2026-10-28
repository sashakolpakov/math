import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.ConcreteFrames
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TranslationFrameCoefficients

/-! # Translation Log -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.TranslationLog.Construction

noncomputable section

/-! The original fixed-fiber logarithmic coefficient is the native
coefficient of the translated difference of the actual pulled frames.
This compares the original units in the original tensor coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram.fixedFiberTensorDiagram AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Affine.OpenDiagram.familyAffineCoordinateFunctor AbelianModuli.HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor AbelianModuli.HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor

private theorem translatedFrameCoefficient_of_unit_coordinates
    (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G] [IsIntegral G.left] [Smooth G.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle G.left) (s t : AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame L.sheaf)
    (B : CommAlgCat ℂ) (a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) [IsOpenImmersion a.left]
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension G.hom) → ℂ)
    (hs : a.left.opensRange ≤ s.domain) (ht : a.left.opensRange ≤ t.domain)
    (u : Bˣ)
    (hu : Units.map (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G a).symm.toMonoidHom
      (s.transition t a.left.opensRange hs ht) = u) :
    let e := AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a)
    (Units.map e.symm.toMonoidHom
      (Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B a).symm).toMonoidHom
        (TranslationFrameCoefficients.Construction.translatedFrameTransition G L s t (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v)
          a.left.opensRange hs ht))).val.snd =
      AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms.coefficientUnitLog ((AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B a).symm
        (AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates.coefficientCovector B (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G v))) u := by
  have h := TranslationFrameCoefficients.Construction.translatedFrameTransition_nativeCoefficient G L s t B a v hs ht
  dsimp only at h ⊢
  exact h.trans (congrArg
    (AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms.coefficientUnitLog ((AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B a).symm
      (AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates.coefficientCovector B (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G v)))) hu)

/-- Bundled coefficients of an affine fixed-fiber chart. -/
def fixedFiberCoefficientAlgebra (T : Type) [CommRing T] [Algebra ℂ T] : CommAlgCat ℂ :=
  CommAlgCat.of ℂ T

/-- The fixed-fiber inclusion with its bundled coefficient source explicit. -/
def fixedFiberCoefficientInclusion
    (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R)))
    (V : X.left.affineOpens) :
    AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ (fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)) ⟶
      AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X :=
  AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram.fixedFiberTensorInclusion R ℂ X V

variable (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R)))
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover L)
    (V : X.left.affineOpens) (i j : C.cover.I₀)
    (hi : V.1 ≤ (C.cover.f i).opensRange) (hj : V.1 ≤ (C.cover.f j).opensRange)

local instance nativeFixedFiberOpen : IsOpenImmersion (fixedFiberCoefficientInclusion R X V).left :=
  AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram.fixedFiberTensorInclusion_open R ℂ X V

private theorem pulled_frame_domain
    {X Y : Scheme.{0}} {M : Y.Modules} (f : X ⟶ Y) (s : AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M) :
    (s.pullbackBy f).domain = f ⁻¹ᵁ s.domain := rfl

private theorem cover_frame_domain
    {X : Scheme.{0}} {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
    (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover L) (k : C.cover.I₀) :
    (C.localFrame k).domain = (C.cover.f k).opensRange := rfl

/-- The pulled frame is defined on the fixed-fiber affine chart. -/
theorem fixedFiberFrameSupport
    (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R)))
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover L)
    (V : X.left.affineOpens) (k : C.cover.I₀) (hk : V.1 ≤ (C.cover.f k).opensRange) :
    (fixedFiberCoefficientInclusion R X V).left.opensRange ≤
      ((C.localFrame k).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X)).domain := by
  rw [pulled_frame_domain, cover_frame_domain]
  exact (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range R ℂ X V).le.trans
    ((AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X).preimage_mono hk)

def fixedFiberFrameTransitionOnRange :
    Γ((AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left, (fixedFiberCoefficientInclusion R X V).left.opensRange)ˣ :=
  ((C.localFrame i).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X)).transition
    ((C.localFrame j).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X))
    (fixedFiberCoefficientInclusion R X V).left.opensRange
    (fixedFiberFrameSupport R X L C V i hi)
    (fixedFiberFrameSupport R X L C V j hj)

theorem fixedFiberFrameTransitionOnRange_coordinates :
    Units.map
      (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ
        (fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)) (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
        (fixedFiberCoefficientInclusion R X V)).symm.toMonoidHom
      (fixedFiberFrameTransitionOnRange R X L C V i j hi hj) =
      AbelianModuli.ReferenceFamily.FixedFiber.LineLogCocycle.fixedFiberFrameReducedUnit R ℂ X (fun a => (C.cover.f a).opensRange)
        C.transitions V i j hi hj := by
  let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
  let B := fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
  let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := fixedFiberCoefficientInclusion R X V
  let e := AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G a
  let p := AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X
  let s := (C.localFrame i).pullbackBy p
  let t := (C.localFrame j).pullbackBy p
  let hR := AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range R ℂ X V
  have hframe := congrArg Units.val (ConcreteFrames.Construction.localLineFrame_transition_transport s t hR
    (hR.le.trans (p.preimage_mono hi)) (hR.le.trans (p.preimage_mono hj))
    (p.preimage_mono hi) (p.preimage_mono hj))
  have hunit := congrArg Units.val
    (ConcreteFrames.Construction.fixedFiberReducedUnit_actualFrameTransition R ℂ X L C V i j hi hj).symm
  apply Units.ext
  apply e.injective
  change e (e.symm (fixedFiberFrameTransitionOnRange R X L C V i j hi hj).val) = _
  rw [RingEquiv.apply_symm_apply]
  apply (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hR).injective
  exact hframe.trans hunit

variable [IsIntegral (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)]
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom) → ℂ)

private theorem originalFixedFiberConormalEquiv_eq_presentation :
    AbelianModuli.ReferenceFamily.FixedFiber.ConstantDerivations.fixedFiberConormalCoefficientEquiv R X V =
      AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
        (fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V))
        (fixedFiberCoefficientInclusion R X V) := rfl

private theorem originalFixedFiberLog_coefficient_formula
    (l : AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityConormal ℂ (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) →ₗ[ℂ] ℂ) :
    let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
    let B := fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
    let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := fixedFiberCoefficientInclusion R X V
    AbelianModuli.ReferenceFamily.FixedFiber.LineLogCocycle.fixedFiberLineLogCoefficient R X (fun b => (C.cover.f b).opensRange) C.transitions
      l V i j hi hj =
    AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms.coefficientUnitLog ((AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B a).symm
      (AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates.coefficientCovector B l))
      (AbelianModuli.ReferenceFamily.FixedFiber.LineLogCocycle.fixedFiberFrameReducedUnit R ℂ X (fun b => (C.cover.f b).opensRange)
        C.transitions V i j hi hj) := by
  let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
  let B := fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
  let u := AbelianModuli.ReferenceFamily.FixedFiber.LineLogCocycle.fixedFiberFrameReducedUnit R ℂ X (fun b => (C.cover.f b).opensRange)
    C.transitions V i j hi hj
  exact congrArg (fun e : Derivation ℂ B B ≃ₗ[B]
      (AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityConormal ℂ G →ₗ[ℂ] B) =>
      AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms.coefficientUnitLog (e.symm (AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates.coefficientCovector B l)) u)
    (originalFixedFiberConormalEquiv_eq_presentation R X V)

private theorem fixedFiber_sourceFrames_coefficient
    (u : (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)ˣ)
    (hu : Units.map (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ
        (fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)) (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
        (fixedFiberCoefficientInclusion R X V)).symm.toMonoidHom
      (((C.localFrame i).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X)).transition ((C.localFrame j).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X)) (fixedFiberCoefficientInclusion R X V).left.opensRange (fixedFiberFrameSupport R X L C V i hi) (fixedFiberFrameSupport R X L C V j hj)) = u) :
    let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
    let B := fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
    let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := fixedFiberCoefficientInclusion R X V
    let e := AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a)
    (Units.map e.symm.toMonoidHom
      (Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B a).symm).toMonoidHom
        (TranslationFrameCoefficients.Construction.translatedFrameTransition G (L.pullback (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X)) ((C.localFrame i).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X)) ((C.localFrame j).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X)) (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v)
          a.left.opensRange (fixedFiberFrameSupport R X L C V i hi) (fixedFiberFrameSupport R X L C V j hj)))).val.snd =
      AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms.coefficientUnitLog ((AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B a).symm
        (AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates.coefficientCovector B (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G v))) u := by
  exact translatedFrameCoefficient_of_unit_coordinates (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) (L.pullback (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X)) ((C.localFrame i).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X)) ((C.localFrame j).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X))
    (fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)) (fixedFiberCoefficientInclusion R X V)
    v (fixedFiberFrameSupport R X L C V i hi) (fixedFiberFrameSupport R X L C V j hj) u hu

/-- The native translated-frame coefficient equals the actual coefficient
used by the original fixed-fiber line-logarithm cocycle. -/
theorem fixedFiberLineLogCoefficient_eq_translationCoefficient :
    let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
    let B := fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
    let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := fixedFiberCoefficientInclusion R X V
    let p := AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X
    let s := (C.localFrame i).pullbackBy p
    let t := (C.localFrame j).pullbackBy p
    let hs := fixedFiberFrameSupport R X L C V i hi
    let ht := fixedFiberFrameSupport R X L C V j hj
    let e := AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a)
    (Units.map e.symm.toMonoidHom
      (Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B a).symm).toMonoidHom
        (TranslationFrameCoefficients.Construction.translatedFrameTransition G (L.pullback p) s t (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v)
          a.left.opensRange hs ht))).val.snd =
      AbelianModuli.ReferenceFamily.FixedFiber.LineLogCocycle.fixedFiberLineLogCoefficient R X (fun b => (C.cover.f b).opensRange) C.transitions
        (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G v) V i j hi hj := by
  let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
  let B := fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
  let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := fixedFiberCoefficientInclusion R X V
  let p := AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X
  let s := (C.localFrame i).pullbackBy p
  let t := (C.localFrame j).pullbackBy p
  let u := AbelianModuli.ReferenceFamily.FixedFiber.LineLogCocycle.fixedFiberFrameReducedUnit R ℂ X (fun b => (C.cover.f b).opensRange)
    C.transitions V i j hi hj
  have hc := fixedFiberFrameTransitionOnRange_coordinates R X L C V i j hi hj
  change Units.map (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G a).symm.toMonoidHom
    (s.transition t a.left.opensRange (fixedFiberFrameSupport R X L C V i hi)
      (fixedFiberFrameSupport R X L C V j hj)) = u at hc
  have hn := fixedFiber_sourceFrames_coefficient (R := R) (X := X) (L := L)
    (C := C) (V := V) (i := i) (j := j) (hi := hi) (hj := hj) (v := v) u hc
  have hf := originalFixedFiberLog_coefficient_formula R X L C V i j hi hj
    (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G v)
  refine Eq.trans (b := AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms.coefficientUnitLog
    ((AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B a).symm
      (AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates.coefficientCovector B (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G v))) u) ?_ ?_
  · convert hn using 2
  · have hrev := hf.symm
    convert hrev using 2

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.TranslationLog.Construction
