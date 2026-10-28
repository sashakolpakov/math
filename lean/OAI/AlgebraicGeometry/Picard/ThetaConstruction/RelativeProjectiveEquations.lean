import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeMinimalFrameQuotient
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeMinimalNormalization
import OAI.RepresentationTheory.Theta.Geometric.Minimal

/-! # Relative Projective Equations -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeProjectiveEquations.Geometric

noncomputable section

/-! An actual smooth projective varying family with trivial closed-fiber line
bundle has a normalized-frame scheme cut out by exactly H1-many
equations. Its Cech model, minimal complex, rank-one generator, and
normalization unit are all constructed internally. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

open OAI.RepresentationTheory.Theta.Geometric.Minimal

universe u

def relativeProjectiveClosedFiberH1 {X S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    (π : X ⟶ S) (PP : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk π)) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : ℕ :=
  Module.finrank Γ(Spec (S.residueField (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint S)), ⊤)
    ((Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.target (π.fiberι (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint S))
      (π.fiberToSpecResidueField (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint S)) L.sheaf
      (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover (Over.mk π) PP)).sc' 0 1 2).homology

variable {X S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)] [IsNoetherianRing Γ(S, ⊤)]
    [IsLocallyNoetherian S]
    (π : X ⟶ S) [IsProper π] [Smooth π] [GeometricallyConnected π]
    (PP : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk π))
    (s : S ⟶ X) (hs : s ≫ π = 𝟙 S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (eM : (Scheme.Modules.pullback (π.fiberι (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint S))).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint S)))

include PP eM in
theorem exists_relativeProjective_frame_equations
    (D : FormalGeometry.Completion.Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf) :
    ∃ (n : ℕ) (v : Fin n → Γ(S, ⊤)), n = relativeProjectiveClosedFiberH1 π PP L ∧
      Ideal.span (Set.range v) ≤ IsLocalRing.maximalIdeal Γ(S, ⊤) ∧
    Nonempty (D.rigidifiedFrameScheme s hs r ≅ RepresentationTheory.Theta.Geometric.Affine.QuotientPoints.affineQuotientScheme S (Ideal.span (Set.range v))) := by
  have : Flat (Over.mk π).hom := inferInstanceAs (Flat π)
  obtain ⟨C, φ, _, ⟨P⟩, hφ⟩ := RepresentationTheory.Theta.Geometric.Local.ProjectiveCechModel.exists_local_projective_cech_model (Over.mk π) PP L
  let U := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover (Over.mk π) PP
  have hU := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.covers (Over.mk π) PP
  have ha := fun n (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex _ n) =>
    Quotients.FiniteDescent.ProjectiveCechFlat.Construction.ProjectiveCechComplex.intersection_affine (Over.mk π) PP n i.1
  obtain ⟨i, hi⟩ := RepresentationTheory.Theta.Geometric.Local.AxisCechChart.exists_axis_cech_chart s U hU
  obtain ⟨e, hu⟩ := RelativeMinimalNormalization.Geometric.exists_relativeProjective_minimal_normalization π PP s hs L r U hU ha
    φ hφ P i hi eM
  let basis := Module.finBasis Γ(S, ⊤) P.complex.X₂
  refine ⟨Module.finrank Γ(S, ⊤) P.complex.X₂, fun j => basis.repr (P.complex.f (e 1)) j,
    ?_, RepresentationTheory.Theta.Geometric.MinimalEquationIdeal.minimalEquationIdeal_le_maximal P basis e,
    ⟨RelativeMinimalFrameQuotient.Geometric.relativeProjective_minimalFrameQuotientIso π PP s hs L r U hU ha φ hφ P basis e i hi hu eM D⟩⟩
  let x := RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint S
  let f := π.fiberι x
  let ρ := π.fiberToSpecResidueField x
  let g := S.fromSpecResidueField x
  have hp : IsPullback f ρ π g := IsPullback.of_hasPullback π g
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : IsLocalHom g.appTop.hom := RepresentationTheory.Theta.Geometric.Local.ClosedPointScalars.affineLocalResidue_isLocalHom S
  have := Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso f π ρ g L.sheaf U φ hp ha hφ
  have hfield : IsField Γ(Spec (S.residueField x), ⊤) := by
    let : Field Γ(Spec (S.residueField x), ⊤) := Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField (S.residueField x)
    exact Field.toIsField _
  exact RepresentationTheory.Theta.Geometric.Minimal.minimal_middle_finrank_eq_geometric_H1 f π ρ g hp.w L.sheaf U φ P hfield

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeProjectiveEquations.Geometric
