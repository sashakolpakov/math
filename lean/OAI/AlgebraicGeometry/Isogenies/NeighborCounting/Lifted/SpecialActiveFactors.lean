import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GraphLineComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.MixedLineKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.PlaneKernels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.MultiplicativeKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FactorSquares

/-! # Special Active Factors -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.SpecialActiveFactors

noncomputable section

/-! Each actual specialized active carrier has the prescribed native
factorization criterion inside the original source PEL point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.BlockInclusions OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FactorSquares OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMixedLineTransport

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)

variable {L : Type} [Field L] [Algebra R L]
  (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q (OrdinarySplitting.Ordinary.liftedActiveBlock j hsplit labels l))

local notation "A" => OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary.liftedActiveBlock j hsplit labels l
local notation "e" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (O.splitting x 1 0)
local notation "a" => OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.BlockInclusions.liftedGeometricOriginalBlockIso j hsplit labels l 1 0

theorem liftedSpecial_graph_line_factor (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (z : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    (∃ h : T ⟶ (C.geometricSpecialKernel R L q A residueIso J.val false).carrier,
      h ≫ (C.geometricSpecialKernel R L q A residueIso J.val false).inclusion ≫ ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false))))) ≫
      l.geometricFamilyIso.abelian.hom) = z) ↔
    ∃ h : T ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) q (C.geometricLineEquiv R L q A residueIso e a J)).X,
      h ≫ (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e (C.geometricLineEquiv R L q A residueIso e a J)).hom.hom ≫ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action 1 (labels (0, false))) = z :=
  Kernel.FactorSquares.factor_iff_of_two_squares
    ((Grp.forget _).mapIso (C.geometricGraphIndependentLineIso R L q A residueIso e a J))
    (C.geometricSpecialKernel R L q A residueIso J.val false).inclusion
    (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e (C.geometricLineEquiv R L q A residueIso e a J)).hom.hom (a).hom.hom.hom (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action 1 (labels (0, false))) ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false))))) ≫
      l.geometricFamilyIso.abelian.hom)
    (C.geometricGraphIndependentLine_inclusion R L q A residueIso e a J)
    (Geometric.BlockInclusions.liftedGeometricOriginalBlockIso_inclusion j hsplit labels l 1 0) z

theorem liftedSpecial_mixed_line_factor (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (z : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    (∃ h : T ⟶ (C.geometricSpecialKernel R L q A residueIso J.val true).carrier,
      h ≫ (C.geometricSpecialKernel R L q A residueIso J.val true).inclusion ≫ ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false))))) ≫
      l.geometricFamilyIso.abelian.hom) = z) ↔
    ∃ h : T ⟶ (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q 1 1 ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) q (C.geometricLineEquiv R L q A residueIso e a J)).X,
      h ≫ (ActiveMixedLineTransport.chosenActiveMixedLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e (C.geometricLineEquiv R L q A residueIso e a J)).hom.hom ≫ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action 1 (labels (0, false))) = z :=
  Kernel.FactorSquares.factor_iff_of_two_squares
    ((Grp.forget _).mapIso (C.geometricMixedIndependentLineIso R L q A residueIso e a J))
    (C.geometricSpecialKernel R L q A residueIso J.val true).inclusion
    (ActiveMixedLineTransport.chosenActiveMixedLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e (C.geometricLineEquiv R L q A residueIso e a J)).hom.hom (a).hom.hom.hom (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action 1 (labels (0, false))) ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false))))) ≫
      l.geometricFamilyIso.abelian.hom)
    (C.geometricMixedIndependentLine_inclusion R L q A residueIso e a J)
    (Geometric.BlockInclusions.liftedGeometricOriginalBlockIso_inclusion j hsplit labels l 1 0) z

theorem liftedSpecial_plane_factor
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (z : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    (∃ h : T ⟶ (C.geometricSpecialKernel R L q A residueIso ⊤ false).carrier,
      h ≫ (C.geometricSpecialKernel R L q A residueIso ⊤ false).inclusion ≫ ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false))))) ≫
      l.geometricFamilyIso.abelian.hom) = z) ↔
    ∃ h : T ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) q).X,
      h ≫ (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e).hom.hom ≫ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action 1 (labels (0, false))) = z :=
  Kernel.FactorSquares.factor_iff_of_two_squares
    ((Grp.forget _).mapIso (C.geometricGraphIndependentPlaneIso R L q A residueIso e a))
    (C.geometricSpecialKernel R L q A residueIso ⊤ false).inclusion
    (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e).hom.hom (a).hom.hom.hom (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action 1 (labels (0, false))) ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false))))) ≫
      l.geometricFamilyIso.abelian.hom)
    (C.geometricGraphIndependentPlane_inclusion R L q A residueIso e a)
    (Geometric.BlockInclusions.liftedGeometricOriginalBlockIso_inclusion j hsplit labels l 1 0) z

theorem liftedSpecial_multiplicative_factor
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (z : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    (∃ h : T ⟶ (C.geometricSpecialKernel R L q A residueIso ⊥ true).carrier,
      h ≫ (C.geometricSpecialKernel R L q A residueIso ⊥ true).inclusion ≫ ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false))))) ≫
      l.geometricFamilyIso.abelian.hom) = z) ↔
    ∃ h : T ⟶ (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q 1 1).X,
      h ≫ (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e).hom.hom ≫ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action 1 (labels (0, false))) = z :=
  Kernel.FactorSquares.factor_iff_of_two_squares
    ((Grp.forget _).mapIso (C.geometricIndependentMultiplicativeIso R L q A residueIso e a))
    (C.geometricSpecialKernel R L q A residueIso ⊥ true).inclusion
    (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e).hom.hom (a).hom.hom.hom (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action 1 (labels (0, false))) ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false))))) ≫
      l.geometricFamilyIso.abelian.hom)
    (C.geometricIndependentMultiplicative_inclusion R L q A residueIso e a)
    (Geometric.BlockInclusions.liftedGeometricOriginalBlockIso_inclusion j hsplit labels l 1 0) z

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.SpecialActiveFactors
