import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharZeroFibers
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeStalkParameters
import OAI.RepresentationTheory.Theta.Geometric.CechDimensionComparison

/-! # Zero Picard Equation Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroPicardEquationBound

noncomputable section

/-! Every stalk of the relative Picard zero parameter over a rational base
has at most g frame equations. The argument uses its actual trivial fiber
line and the characteristic-zero H1 bound, without reducing the base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry.Scheme.Modules

open OAI.RepresentationTheory.Theta.Geometric.CechDimensionComparison OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeStalkParameters.Geometric.RelativeRigidifiedCharts

theorem rationalFamily_localFiber_trivialLine_H1_le_dimension
    {S : Scheme} {g : ℕ} (qS : S ⟶ Spec (.of ℚ))
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
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
  let : CharZero (U.left.residueField x) := CharZeroFibers.charZero_of_rational_scheme_map (b ≫ U.hom ≫ qS)
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
    (CharZeroFibers.charZeroAbelian_cartesian_structureCechH1_finrank_le (k := U.left.residueField x)
      A P (b ≫ U.hom) f ρ hf V hV haV)

theorem rationalFamily_zero_stalk_H1_le_dimension
    {S : Scheme} {g : ℕ} (qS : S ⟶ Spec (.of ℚ))
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    {B : Over S} [IsLocallyNoetherian B.left]
    (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A.scheme B) (z : (Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).left) :
    Picard.ThetaConstruction.RelativeProjectiveEquations.Geometric.relativeProjectiveClosedFiberH1
      (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A.scheme (Picard.ThetaConstruction.RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkParameter B ((Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z))).hom
      (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A.scheme (Picard.ThetaConstruction.RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkParameter B ((Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z)) P)
      (D.line (Picard.ThetaConstruction.RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkMap B ((Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z))) ≤ g := by
  obtain ⟨eM⟩ := Picard.ThetaConstruction.RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalk_fiber_trivial P D z
  exact rationalFamily_localFiber_trivialLine_H1_le_dimension qS A P _ _ _ eM

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroPicardEquationBound
