import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.StructureOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.BaseCechCoefficientCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.SchemeTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.BaseChangeCoherence
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeStalkParameters
import OAI.RepresentationTheory.Theta.Geometric.CechDimensionComparison

/-! # Structure Picard Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A genuine structure-sheaf H1 bound on the original field fibers
bounds the local Picard equations, in every characteristic. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry.Scheme.Modules

open OAI.RepresentationTheory.Theta.Geometric.CechDimensionComparison OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeStalkParameters.Geometric.RelativeRigidifiedCharts

def Abelian.Schemes.AbelianScheme.HasFieldStructureH1Bound {S : Scheme} {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) : Prop :=
  ∀ (K : Type) [Field K] (b : Spec (.of K) ⟶ S),
    (A.pullback b).structureH1Dimension ≤ g

theorem Abelian.Schemes.AbelianScheme.HasFieldStructureH1Bound.pullback {S T : Scheme} {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g S} (h : A.HasFieldStructureH1Bound) (f : T ⟶ S) :
    (A.pullback f).HasFieldStructureH1Bound := by
  intro K _ b
  exact (((A.pullback f).pullback b).structureH1Dimension_eq_of_iso
    (A.pullback (b ≫ f)) (A.pullbackCompIso f b).symm).le.trans (h K (b ≫ f))

theorem Field.StructurePicardBound.fieldBound_cartesian_structureCechH1_finrank_le
    {S Y : Scheme} {k : Type} [Field k] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (hH1 : A.HasFieldStructureH1Bound)
    (b : Spec (.of k) ⟶ S) (f : Y ⟶ A.scheme.left) (ρ : Y ⟶ Spec (.of k))
    (hp : IsPullback f ρ A.scheme.hom b)
    {I : Type} [LinearOrder I] (U : I → Y.Opens)
    (hU : IsOpenCover U) (haU : ∀ i, IsAffineOpen (U i)) :
    Module.finrank Γ(Spec (.of k), ⊤)
      ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex ρ (Line.Bundles.structureModule Y) U).sc' 0 1 2).homology ≤ g := by
  let e : Over.mk ρ ≅ (A.pullback b).scheme :=
    Over.isoMk hp.isoPullback hp.isoPullback_hom_snd
  let B := (A.pullback b).transport e.symm
  have : IsProper ρ := B.proper
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from ρ]; infer_instance⟩
  have : (Line.Bundles.structureModule Y).IsQuasicoherent :=
    Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (Line.Bundles.LineBundle.trivial Y)
  have h := (B.structureH1Dimension_eq_of_iso (A.pullback b) e).le.trans (hH1 k b)
  exact (Ordered.BaseCechCoefficientCohomology.orderedBaseCech_H1_finrank_coefficient ρ (Line.Bundles.structureModule Y) U hU haU).le.trans h

theorem Field.StructurePicardBound.fieldBound_localFiber_trivialLine_H1_le_dimension
    {S : Scheme} {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (hH1 : A.HasFieldStructureH1Bound)
    (U : Over S) [IsAffine U.left] [IsLocalRing Γ(U.left, ⊤)]
    (PP : Projective.ProjectivePresentations.ProjectivePresentation (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A.scheme U))
    (L : Line.Bundles.LineBundle (U ⊗ A.scheme).left)
    (eM : (Scheme.Modules.pullback ((FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A.scheme U).hom.fiberι
      (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint U.left))).obj L.sheaf ≅
        Line.Bundles.structureModule ((FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A.scheme U).hom.fiber (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint U.left))) :
    Picard.ThetaConstruction.RelativeProjectiveEquations.Geometric.relativeProjectiveClosedFiberH1 (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A.scheme U).hom PP L ≤ g := by
  let π := (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A.scheme U).hom
  let x := RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint U.left
  let j := π.fiberι x
  let ρ := π.fiberToSpecResidueField x
  let b := U.left.fromSpecResidueField x
  let a := (snd U A.scheme).left
  let f := j ≫ a
  have hj : IsPullback j ρ π b := IsPullback.of_hasPullback π b
  have ha : IsPullback a π A.scheme.hom U.hom :=
    (IsPullback.of_hasPullback U.hom A.scheme.hom).flip
  have hf : IsPullback f ρ A.scheme.hom (b ≫ U.hom) := hj.paste_horiz ha
  let : IsAffineHom j := MorphismProperty.of_isPullback (P := @IsAffineHom) hj.flip inferInstance
  let V := fun i => j ⁻¹ᵁ Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A.scheme U) PP i
  have hV : IsOpenCover V := by
    change iSup (fun i => j ⁻¹ᵁ Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A.scheme U) PP i) = ⊤
    rw [← j.preimage_iSup, Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.covers]
    rfl
  have haV : ∀ i, IsAffineOpen (V i) :=
    fun i => (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.affine (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A.scheme U) PP i).preimage j
  have hi := RepresentationTheory.Theta.Geometric.CechDimensionComparison.orderedBaseCech_H1_finrank_iso ρ eM V
  exact hi.le.trans
    (HilbertConstruction.Field.StructurePicardBound.fieldBound_cartesian_structureCechH1_finrank_le (k := U.left.residueField x)
      A hH1 (b ≫ U.hom) f ρ hf V hV haV)

theorem Field.StructurePicardBound.fieldBound_zero_stalk_H1_le_dimension
    {S : Scheme} {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (hH1 : A.HasFieldStructureH1Bound)
    {B : Over S} [IsLocallyNoetherian B.left]
    (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A.scheme B) (z : (Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).left) :
    Picard.ThetaConstruction.RelativeProjectiveEquations.Geometric.relativeProjectiveClosedFiberH1
      (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A.scheme (Picard.ThetaConstruction.RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkParameter B ((Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z))).hom
      (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A.scheme (Picard.ThetaConstruction.RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkParameter B ((Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z)) P)
      (D.line (Picard.ThetaConstruction.RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkMap B ((Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z))) ≤ g := by
  obtain ⟨eM⟩ := Picard.ThetaConstruction.RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalk_fiber_trivial P D z
  exact HilbertConstruction.Field.StructurePicardBound.fieldBound_localFiber_trivialLine_H1_le_dimension A hH1 _ _ _ eM

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
