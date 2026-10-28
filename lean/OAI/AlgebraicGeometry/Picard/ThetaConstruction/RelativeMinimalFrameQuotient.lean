import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeMinimalQuotientFrame
import OAI.RepresentationTheory.Theta.Geometric.NormalizationUnit
import OAI.RepresentationTheory.Theta.Geometric.Affine.TestMonomorphisms
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameMonomorphism

/-! # Relative Minimal Frame Quotient -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeMinimalFrameQuotient.Geometric

noncomputable section

/-! The actual normalized-frame scheme over a local affine base is the
closed quotient by the original minimal differential coefficients. -/

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
theorem relativeProjective_minimalFrame_hasLift_iff
    (D : FormalGeometry.Completion.Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)
    (T : Over S) [IsAffine T.left] :
    Nonempty (T ⟶ D.rigidifiedFrameScheme s hs r) ↔
      RepresentationTheory.Theta.Geometric.MinimalEquationIdeal.minimalEquationIdeal P basis e ≤ RingHom.ker T.hom.appTop.hom := by
  constructor
  · rintro ⟨p⟩
    let f := pullback.fst π T.hom
    let ρ := pullback.snd π T.hom
    have hp : IsPullback f ρ π T.hom := IsPullback.of_hasPullback π T.hom
    let b := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection f ρ π T.hom hp s hs
    have hb := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_snd f ρ π T.hom hp s hs
    have hx := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π T.hom hp s hs
    have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
    have := Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso f π ρ T.hom L.sheaf U φ hp ha hφ
    let v := (D.normalizedTrivializationPointEquiv f ρ T.hom hp s hs b hb hx r).symm p
    have hn := RepresentationTheory.Theta.Geometric.NormalizationUnit.trivialization_exists_normalizedSection f ρ b hb T.hom s hx L.sheaf r v.val.symm
    exact (RepresentationTheory.Theta.Geometric.Normalized.SectionEquations.normalized_geometric_sections_equations f b T.hom s hx π ρ hp.w hs hb
      L.sheaf U r i hi φ hU P basis e hu).mp hn
  · intro h
    obtain ⟨p⟩ := (RepresentationTheory.Theta.Geometric.Affine.QuotientPoints.affineQuotientScheme_hasLift_iff S (RepresentationTheory.Theta.Geometric.MinimalEquationIdeal.minimalEquationIdeal P basis e) T).mpr h
    obtain ⟨v⟩ := RelativeMinimalQuotientFrame.Geometric.relativeProjective_minimalQuotient_hasNormalizedFrame π PP s hs L r U hU ha φ hφ
      P basis e i hi hu eM D
    exact ⟨p ≫ v⟩

include PP hU ha hφ hu eM in
def relativeProjective_minimalFrameQuotientIso
    (D : FormalGeometry.Completion.Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf) :
    D.rigidifiedFrameScheme s hs r ≅ RepresentationTheory.Theta.Geometric.Affine.QuotientPoints.affineQuotientScheme S (RepresentationTheory.Theta.Geometric.MinimalEquationIdeal.minimalEquationIdeal P basis e) := by
  let : IsProper (Over.mk π).hom := inferInstanceAs (IsProper π)
  let : Smooth (Over.mk π).hom := inferInstanceAs (Smooth π)
  let : GeometricallyConnected (Over.mk π).hom := inferInstanceAs (GeometricallyConnected π)
  have : Mono (D.rigidifiedFrameScheme s hs r).hom :=
    RelativeFrameRigidity.Geometric.relativeProjective_rigidifiedFrame_mono PP s hs D r
  exact RepresentationTheory.Theta.Geometric.Affine.TestMonomorphisms.monoAffineQuotientIso (D.rigidifiedFrameScheme s hs r) (RepresentationTheory.Theta.Geometric.MinimalEquationIdeal.minimalEquationIdeal P basis e)
    (fun T _ => relativeProjective_minimalFrame_hasLift_iff π PP s hs L r U hU ha φ hφ P basis e i hi hu eM D T)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeMinimalFrameQuotient.Geometric
