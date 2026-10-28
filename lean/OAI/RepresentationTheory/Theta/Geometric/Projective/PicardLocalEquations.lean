import OAI.RepresentationTheory.Theta.Geometric.MinimalFrameQuotient
import OAI.RepresentationTheory.Theta.Geometric.MinimalNormalization
import OAI.RepresentationTheory.Theta.Geometric.Minimal

/-! # Picard Local Equations -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.PicardLocalEquations

noncomputable section

/-! A flat projective constant family with trivial closed-fiber line
bundle has a normalized-frame scheme cut out by exactly H1-many
equations. Its Cech model, minimal complex, rank-one generator, and
normalization unit are all constructed internally. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

def projectiveClosedFiberH1 {X S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    (π : X ⟶ S) (PP : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk π)) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : ℕ :=
  Module.finrank Γ(Spec (S.residueField (Local.AxisCechChart.affineLocalClosedPoint S)), ⊤)
    ((AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.target (π.fiberι (Local.AxisCechChart.affineLocalClosedPoint S))
      (π.fiberToSpecResidueField (Local.AxisCechChart.affineLocalClosedPoint S)) L.sheaf
      (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover (Over.mk π) PP)).sc' 0 1 2).homology

variable {K : Type u} [Field K] [IsAlgClosed K]
    {A X S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)] [IsNoetherianRing Γ(S, ⊤)]
    (a : A ⟶ Spec (.of K)) [IsIntegral A] [IsProper a]
    (π : X ⟶ S) [IsProper π] [Flat π] (PP : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk π))
    (q : X ⟶ A) (t : S ⟶ Spec (.of K)) (hX : IsPullback q π a t)
    (s : S ⟶ X) (hs : s ≫ π = 𝟙 S) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (eM : (Scheme.Modules.pullback (π.fiberι (Local.AxisCechChart.affineLocalClosedPoint S))).obj L.sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber (Local.AxisCechChart.affineLocalClosedPoint S)))

include hX eM in
theorem exists_projective_frame_equations
    (D : AlgebraicGeometry.FormalGeometry.Completion.Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf) :
    ∃ (n : ℕ) (v : Fin n → Γ(S, ⊤)), n = projectiveClosedFiberH1 π PP L ∧
      Ideal.span (Set.range v) ≤ IsLocalRing.maximalIdeal Γ(S, ⊤) ∧
    Nonempty (D.rigidifiedFrameScheme s hs r ≅ Affine.QuotientPoints.affineQuotientScheme S (Ideal.span (Set.range v))) := by
  have : Flat (Over.mk π).hom := inferInstanceAs (Flat π)
  obtain ⟨C, φ, _, ⟨P⟩, hφ⟩ := Local.ProjectiveCechModel.exists_local_projective_cech_model (Over.mk π) PP L
  let U := AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover (Over.mk π) PP
  have hU := AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.covers (Over.mk π) PP
  have ha := fun n (i : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex _ n) =>
    AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechFlat.Construction.ProjectiveCechComplex.intersection_affine (Over.mk π) PP n i.1
  obtain ⟨i, hi⟩ := Local.AxisCechChart.exists_axis_cech_chart s U hU
  obtain ⟨e, hu⟩ := MinimalNormalization.exists_geometric_minimal_normalization a π q t hX s hs L r U hU ha
    φ hφ P i hi eM
  let basis := Module.finBasis Γ(S, ⊤) P.complex.X₂
  refine ⟨Module.finrank Γ(S, ⊤) P.complex.X₂, fun j => basis.repr (P.complex.f (e 1)) j,
    ?_, MinimalEquationIdeal.minimalEquationIdeal_le_maximal P basis e,
    ⟨MinimalFrameQuotient.minimalFrameQuotientIso a π q t hX s hs L r U hU ha φ hφ P basis e i hi hu eM D⟩⟩
  let x := Local.AxisCechChart.affineLocalClosedPoint S
  let f := π.fiberι x
  let ρ := π.fiberToSpecResidueField x
  let g := S.fromSpecResidueField x
  have hp : IsPullback f ρ π g := IsPullback.of_hasPullback π g
  have : L.sheaf.IsQuasicoherent := AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : IsLocalHom g.appTop.hom := Local.ClosedPointScalars.affineLocalResidue_isLocalHom S
  have := AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso f π ρ g L.sheaf U φ hp ha hφ
  have hfield : IsField Γ(Spec (S.residueField x), ⊤) := by
    let : Field Γ(Spec (S.residueField x), ⊤) := AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField (S.residueField x)
    exact Field.toIsField _
  exact Minimal.minimal_middle_finrank_eq_geometric_H1 f π ρ g hp.w L.sheaf U φ P hfield

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.PicardLocalEquations
