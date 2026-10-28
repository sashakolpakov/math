import OAI.RepresentationTheory.Theta.Geometric.MinimalQuotientGeometry
import OAI.RepresentationTheory.Theta.Geometric.Normalized.SectionEquations
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeLocalFrames
import OAI.RepresentationTheory.Theta.Geometric.SectionAxisBaseChange

/-! # Relative Minimal Quotient Frame -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeMinimalQuotientFrame.Geometric

noncomputable section

/-! The actual minimal-equation quotient carries a normalized frame.
The frame condition follows from its original trivial closed fiber and
properness of the original varying family. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u
variable {X S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)] [IsLocallyNoetherian S]
    (π : X ⟶ S) [IsProper π] [Smooth π] [GeometricallyConnected π]
    (PP : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk π)) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    {I : Type u} [LinearOrder I] [Finite I] (U : I → X.Opens) (hU : iSup U = ⊤)
    (ha : ∀ (n : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex I n), IsAffineOpen (∏ᶜ fun k => U (i.1 k)))
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π L.sheaf U)
    (hφ : ∀ (V : Type u) [AddCommGroup V] [Module Γ(S, ⊤) V],
      QuasiIso (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map V φ))
    (P : Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2)) {J : Type*}
    (basis : Module.Basis J Γ(S, ⊤) P.complex.X₂)
    (e : Γ(S, ⊤) ≃ₗ[Γ(S, ⊤)] P.complex.X₁)
    (i : I) (hi : (⊤ : S.Opens) ≤ s ⁻¹ᵁ Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0
      (Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i))
    (hu : IsUnit (RepresentationTheory.Theta.Geometric.MinimalNormalizedSections.minimalSectionFunctional P (RepresentationTheory.Theta.Geometric.ModelAxisNormalization.modelAxisFunctional s π hs L.sheaf U r i hi φ) (e 1)))
    (eM : (Scheme.Modules.pullback (π.fiberι (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint S))).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint S)))

include PP hU ha hφ hu eM in
theorem relativeProjective_minimalQuotient_hasNormalizedFrame
    (D : FormalGeometry.Completion.Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf) :
    Nonempty (RepresentationTheory.Theta.Geometric.Affine.QuotientPoints.affineQuotientScheme S (RepresentationTheory.Theta.Geometric.MinimalEquationIdeal.minimalEquationIdeal P basis e) ⟶
      D.rigidifiedFrameScheme s hs r) := by
  let Q := RepresentationTheory.Theta.Geometric.Affine.QuotientPoints.affineQuotientScheme S (RepresentationTheory.Theta.Geometric.MinimalEquationIdeal.minimalEquationIdeal P basis e)
  let f := pullback.fst π Q.hom
  let ρ := pullback.snd π Q.hom
  have hp : IsPullback f ρ π Q.hom := IsPullback.of_hasPullback π Q.hom
  let b := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection f ρ π Q.hom hp s hs
  have hb := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_snd f ρ π Q.hom hp s hs
  have hx := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π Q.hom hp s hs
  have : IsAffine Q.left := inferInstanceAs (IsAffine (Spec (.of (Γ(S, ⊤) ⧸ RepresentationTheory.Theta.Geometric.MinimalEquationIdeal.minimalEquationIdeal P basis e))))
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have := Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso f π ρ Q.hom L.sheaf U φ hp ha hφ
  have hkill : RepresentationTheory.Theta.Geometric.MinimalEquationIdeal.minimalEquationIdeal P basis e ≤ RingHom.ker Q.hom.appTop.hom :=
    (RepresentationTheory.Theta.Geometric.Affine.QuotientPoints.affineQuotientScheme_hasLift_iff S (RepresentationTheory.Theta.Geometric.MinimalEquationIdeal.minimalEquationIdeal P basis e) Q).mp ⟨𝟙 Q⟩
  obtain ⟨z, hz⟩ := (RepresentationTheory.Theta.Geometric.Normalized.SectionEquations.normalized_geometric_sections_equations f b Q.hom s hx π ρ hp.w hs hb
    L.sheaf U r i hi φ hU P basis e hu).mpr hkill
  let v := (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback f).obj L.sheaf)).symm z
  have hv : (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b Q.hom s hx L.sheaf r).hom.app ⊤
      (FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback b ((Scheme.Modules.pullback f).obj L.sheaf)
        (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _ v)) = (1 : Γ(Q.left, ⊤)) := by
    have heq : AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback f).obj L.sheaf) v = z :=
      (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback f).obj L.sheaf)).apply_symm_apply z
    exact (congrArg (fun t : Γ((Scheme.Modules.pullback f).obj L.sheaf, ⊤) =>
      (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b Q.hom s hx L.sheaf r).hom.app ⊤
        (FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback b ((Scheme.Modules.pullback f).obj L.sheaf) t)) heq).trans hz
  have ef : (Scheme.Modules.pullback (π.fiberι
      (Q.hom (IsLocalRing.closedPoint (Γ(S, ⊤) ⧸ RepresentationTheory.Theta.Geometric.MinimalEquationIdeal.minimalEquationIdeal P basis e))))).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber
        (Q.hom (IsLocalRing.closedPoint (Γ(S, ⊤) ⧸ RepresentationTheory.Theta.Geometric.MinimalEquationIdeal.minimalEquationIdeal P basis e)))) := by
    change (Scheme.Modules.pullback (π.fiberι ((RepresentationTheory.Theta.Geometric.Affine.QuotientPoints.affineQuotientScheme S
      (RepresentationTheory.Theta.Geometric.MinimalEquationIdeal.minimalEquationIdeal P basis e)).hom (IsLocalRing.closedPoint _)))).obj L.sheaf ≅ _
    rw [RepresentationTheory.Theta.Geometric.MinimalQuotientGeometry.minimalQuotient_closedPoint]
    exact eM
  let : IsProper (Over.mk π).hom := inferInstanceAs (IsProper π)
  let : Smooth (Over.mk π).hom := inferInstanceAs (Smooth π)
  let : GeometricallyConnected (Over.mk π).hom := inferInstanceAs (GeometricallyConnected π)
  have : IsIso v := RelativeLocalFrames.Geometric.relativeProjective_localBaseChange_normalizedSection_isIso PP s hs
    f ρ Q.hom hp b hb hx L r v hv ef
  refine ⟨D.normalizedTrivializationPointEquiv f ρ Q.hom hp s hs b hb hx r ⟨asIso v, ?_⟩⟩
  have he := RepresentationTheory.Theta.Geometric.Normalized.ClosedFiberFrames.rigidifiedSection_endValue b ((Scheme.Modules.pullback f).obj L.sheaf)
    (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b Q.hom s hx L.sheaf r) v
  exact (RepresentationTheory.Theta.Geometric.SectionAxisBaseChange.sectionAxisScalar_frame f b Q.hom s hx L.sheaf r (asIso v)).symm.trans (he.trans hv)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeMinimalQuotientFrame.Geometric
