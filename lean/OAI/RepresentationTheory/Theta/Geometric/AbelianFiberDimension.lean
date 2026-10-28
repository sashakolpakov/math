import OAI.RepresentationTheory.Theta.Geometric.ConstantFiberDimension
import OAI.RepresentationTheory.Theta.Geometric.Projective.PicardLocalEquations
import OAI.RepresentationTheory.Theta.Geometric.ZariskiBaseDimension

/-! # Abelian Fiber Dimension -/

namespace OAI.RepresentationTheory.Theta.Geometric.AbelianFiberDimension

noncomputable section

/-! The number of local Picard equations is the original algebraic
structure-sheaf H1 dimension of the constant complex abelian variety. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

theorem projectiveClosedFiberH1_eq_abelianH1 (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    {X S : Scheme.{0}} [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    (π : X ⟶ S) (PP : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk π))
    (q : X ⟶ A.carrier) (t : S ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (hp : IsPullback q π A.variety.structureMap t) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (eM : (Scheme.Modules.pullback (π.fiberι (Local.AxisCechChart.affineLocalClosedPoint S))).obj L.sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber (Local.AxisCechChart.affineLocalClosedPoint S))) :
    letI := AlgebraicGeometry.SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
    Projective.PicardLocalEquations.projectiveClosedFiberH1 π PP L =
      Module.finrank ℂ (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1) := by
  classical
  let := AlgebraicGeometry.SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
  let := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule A.variety.structureMap (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
  let x := Local.AxisCechChart.affineLocalClosedPoint S
  let j := π.fiberι x
  let ρ := π.fiberToSpecResidueField x
  let g := S.fromSpecResidueField x
  have hj : IsPullback j ρ π g := IsPullback.of_hasPullback π g
  have : IsProper π := PP.proper
  have : IsProper ρ := inferInstanceAs (IsProper (pullback.snd π g))
  have : (π.fiber x).IsSeparated := by
    constructor
    rw [← terminal.comp_from ρ]
    infer_instance
  have : A.carrier.IsSeparated := by
    constructor
    rw [← terminal.comp_from A.variety.structureMap]
    infer_instance
  have : IsAffineHom j := MorphismProperty.of_isPullback (P := @IsAffineHom) hj.flip inferInstance
  let : Field Γ(Spec (S.residueField x), ⊤) := AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField (S.residueField x)
  let : LinearOrder (AlgebraicGeometry.SheafCohomology.CechFiniteCover.Projective.finiteAffineCover A).I₀ :=
    (Fintype.equivFin (AlgebraicGeometry.SheafCohomology.CechFiniteCover.Projective.finiteAffineCover A).I₀).linearOrder
  let U := AlgebraicGeometry.SheafCohomology.CechFiniteCover.Projective.finiteAffineCoverOpen A
  let V := fun i => j ⁻¹ᵁ AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover (Over.mk π) PP i
  have hU := AlgebraicGeometry.SheafCohomology.CechFiniteCover.Projective.finiteAffineCoverOpen_covers A
  have haU := AlgebraicGeometry.SheafCohomology.CechFiniteCover.Projective.finiteAffineCoverOpen_affine A
  have hV : IsOpenCover V := by
    change iSup (fun i => j ⁻¹ᵁ AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover (Over.mk π) PP i) = ⊤
    rw [← j.preimage_iSup, AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.covers]
    rfl
  have haV : ∀ i, IsAffineOpen (V i) :=
    fun i => (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.affine (Over.mk π) PP i).preimage j
  have : (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier).IsQuasicoherent :=
    AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A.carrier)
  have : ((Scheme.Modules.pullback (j ≫ q)).obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier)).IsQuasicoherent :=
    AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A.carrier).pullback (j ≫ q))
  have hfield : IsField Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) := by
    let : Field Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) := AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField ℂ
    exact Field.toIsField _
  have hc := ConstantFiberDimension.geometricCech_H1_finrank_cover_baseChange hfield (j ≫ q) A.variety.structureMap
    ρ (g ≫ t) (hj.paste_horiz hp) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier)
    ((Scheme.Modules.pullback j).obj L.sheaf) (eM ≪≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (j ≫ q)).symm)
    U V hU hV haU haV
  have he := ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.variety.structureMap (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) U).homologyIsoSc'
    0 1 2 (by simp) (by simp)).toLinearEquiv.finrank_eq
  exact hc.trans (he.symm.trans
    ((AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv A.variety.structureMap
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) U hU haU 1).finrank_eq.trans
      (ZariskiBaseDimension.zariskiBase_finrank_complex A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1)))

end

end OAI.RepresentationTheory.Theta.Geometric.AbelianFiberDimension
