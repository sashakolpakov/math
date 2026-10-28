import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.IntegralNaturality
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockInclusion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.InclusionSquares

/-! # Generic Block Inclusion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericBlockInclusion

noncomputable section

/-! The original and evaluated generic native blocks have their actual
ambient inclusions identified by the constructed source isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockPointComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockSplitting
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockInclusion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.IntegralNaturality OAI.AlgebraicGeometry.Isogenies.NeighborCounting.InclusionSquares

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x) (v : EvaluationDVRLifts.EvaluationDVR R L)

theorem evaluatedLiftGenericBlockGroupIso_inclusion (n : ℕ) (τ : Gal(E/ℚ)) :
    (BlockPointComparison.evaluatedLiftGenericBlockGroupIso (F := F) j hsplit l v n τ).hom.hom.hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).map
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n)
          ((l.overEvaluationDVR v).action.map (j.projector iota hsplit n τ))) =
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n)
          ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
            (j.projector iota hsplit n τ))) ≫
      (SourceGroupIso.evaluatedLiftGenericSourceGroupIso (F := F) l v).hom.hom.hom := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R F))
  let h := Spec.map (CommRingCat.ofHom (algebraMap F L))
  let b := Spec.map (CommRingCat.ofHom (algebraMap R v.carrier))
  let g := Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))
  let z := j.projector iota hsplit n τ
  let i₀ := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (l.action.map z)
  let iF := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) ((l.action.pullback f).map z)
  let iV := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) ((l.overEvaluationDVR v).action.map z)
  let e₀ := (Over.pullback h).mapIso
    (Intrinsic.BlockBaseChange.nativeBlockBaseChangeIso j iota hsplit l.polarized.abelian l.action f n τ).symm
  let e₁ := BlockSplitting.evaluatedIntegralBlockIso R F L (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (l.action.map z)) v
  let e₂ := (Over.pullback g).mapIso (LiftBlockIso.evaluatedLiftBlockIso j hsplit l v n τ)
  let a₁ := BlockSplitting.evaluatedIntegralBlockIso R F L l.polarized.abelian.scheme v
  let a₂ := (Over.pullback g).mapIso (l.evaluationActionIso v).polarized.abelian
  change (e₀ ≪≫ e₁ ≪≫ e₂).hom ≫ (Over.pullback g).map iV =
    (Over.pullback h).map iF ≫ (a₁ ≪≫ a₂).hom
  apply InclusionSquares.three_iso_inclusion e₀ e₁ e₂ a₁ a₂
    ((Over.pullback h).map iF) ((Over.pullback h).map ((Over.pullback f).map i₀))
    ((Over.pullback g).map ((Over.pullback b).map i₀)) ((Over.pullback g).map iV)
  · exact InclusionSquares.map_inverse_inclusion (Over.pullback h)
      (Intrinsic.BlockBaseChange.nativeBlockBaseChangeIso j iota hsplit l.polarized.abelian l.action f n τ)
      iF ((Over.pullback f).map i₀)
      (Intrinsic.BlockBaseChange.nativeBlockBaseChangeIso_inclusion j iota hsplit l.polarized.abelian l.action f n τ)
  · exact IntegralNaturality.evaluatedIntegralBlockIso_natural R F L v i₀
  · have he : (LiftBlockIso.evaluatedLiftBlockIso j hsplit l v n τ).hom ≫ iV =
        (Over.pullback b).map i₀ ≫ (l.evaluationActionIso v).polarized.abelian.hom :=
      LiftBlockInclusion.evaluatedLiftBlockGroupIso_inclusion j hsplit l v n τ
    exact ((Over.pullback g).map_comp _ _).symm.trans
      ((congrArg (fun k => (Over.pullback g).map k) he).trans
        ((Over.pullback g).map_comp _ _))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericBlockInclusion
