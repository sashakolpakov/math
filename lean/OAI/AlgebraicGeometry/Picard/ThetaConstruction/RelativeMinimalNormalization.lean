import OAI.RepresentationTheory.Theta.Geometric.NormalizationUnit
import OAI.RepresentationTheory.Theta.Geometric.Local.ClosedPointScalars
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFrameRigidity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification

/-! # Relative Minimal Normalization -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeMinimalNormalization.Geometric

noncomputable section

/-! The rank-one module and its unit axis normalization are derived from
the actual trivial closed fiber of the original varying projective family. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

open OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification.Construction

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
    (P : Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2))
    (i : I) (hi : (⊤ : S.Opens) ≤ s ⁻¹ᵁ Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0
      (Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i))
    (eM : (Scheme.Modules.pullback (π.fiberι (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint S))).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint S)))

include PP hU ha hφ eM in
theorem exists_relativeProjective_minimal_normalization :
    ∃ e : Γ(S, ⊤) ≃ₗ[Γ(S, ⊤)] P.complex.X₁,
      IsUnit (RepresentationTheory.Theta.Geometric.MinimalNormalizedSections.minimalSectionFunctional P (RepresentationTheory.Theta.Geometric.ModelAxisNormalization.modelAxisFunctional s π hs L.sheaf U r i hi φ) (e 1)) := by
  let x := RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint S
  let f := π.fiberι x
  let ρ := π.fiberToSpecResidueField x
  let g := S.fromSpecResidueField x
  have hp : IsPullback f ρ π g := IsPullback.of_hasPullback π g
  let b := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection f ρ π g hp s hs
  have hb := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_snd f ρ π g hp s hs
  have hx := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π g hp s hs
  have : IsLocalHom g.appTop.hom := RepresentationTheory.Theta.Geometric.Local.ClosedPointScalars.affineLocalResidue_isLocalHom S
  let : IsProper (Over.mk π).hom := inferInstanceAs (IsProper π)
  let : Smooth (Over.mk π).hom := inferInstanceAs (Smooth π)
  let : GeometricallyConnected (Over.mk π).hom := inferInstanceAs (GeometricallyConnected π)
  let : IsIso ρ.appTop := AbelianModuli.HilbertConstruction.Projective.UniversalGlobalFunctions.projectivePresentation_baseChange_globalFunctions_isIso PP s hs hp
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have := Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso f π ρ g L.sheaf U φ hp ha hφ
  have hfield : IsField Γ(Spec (S.residueField x), ⊤) := by
    let : Field Γ(Spec (S.residueField x), ⊤) := Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField (S.residueField x)
    exact Field.toIsField _
  have hdim := RepresentationTheory.Theta.Geometric.NormalizationUnit.minimal_first_finrank_of_trivial_geometric_fiber f g π ρ hp.w L.sheaf U φ hU P hfield eM
  let e : Γ(S, ⊤) ≃ₗ[Γ(S, ⊤)] P.complex.X₁ :=
    LinearEquiv.ofFinrankEq _ _ ((Module.finrank_self _).trans hdim.symm)
  exact ⟨e, RepresentationTheory.Theta.Geometric.NormalizationUnit.modelNormalization_unit_of_trivial_fiber f b g s hx π ρ hp.w hs hb
    L.sheaf U r i hi φ hU P e eM⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeMinimalNormalization.Geometric
