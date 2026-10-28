import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GraphLineComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.MixedLineKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.PlaneKernels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.MultiplicativeKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FactorSquares

/-! # Special Factor -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.SpecialFactor

noncomputable section

/-! The original full mixed active carrier identifies with the whole
geometric q-block, retaining the ambient source inclusion. -/

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

theorem liftedSpecial_full_factor
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (z : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    (∃ h : T ⟶ (C.geometricSpecialKernel R L q A residueIso ⊤ true).carrier,
      h ≫ (C.geometricSpecialKernel R L q A residueIso ⊤ true).inclusion ≫ ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false))))) ≫
      l.geometricFamilyIso.abelian.hom) = z) ↔
    ∃ h : T ⟶ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (D.pointDatum x.val).data.polarized
      (D.pointDatum x.val).data.action (labels (0, false)) 1).X,
      h ≫ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action 1 (labels (0, false))) = z := by
  let u := (Grp.forget _).mapIso (C.geometricMixedTopIso R L q A residueIso ≪≫ a)
  have hu : u.hom ≫ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action 1 (labels (0, false))) =
      (C.geometricSpecialKernel R L q A residueIso ⊤ true).inclusion ≫ ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false))))) ≫
      l.geometricFamilyIso.abelian.hom) := by
    change ((C.geometricMixedTopIso R L q A residueIso).hom.hom.hom ≫ (a).hom.hom.hom) ≫
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action 1 (labels (0, false))) = _
    have ha := Geometric.BlockInclusions.liftedGeometricOriginalBlockIso_inclusion j hsplit labels l 1 0
    have hc := C.geometricMixedTopIso_inclusion R L q A residueIso
    exact (Category.assoc (C.geometricMixedTopIso R L q A residueIso).hom.hom.hom
      (a).hom.hom.hom (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
        (D.pointDatum x.val).data.action 1 (labels (0, false)))).trans
      ((congrArg (fun f => (C.geometricMixedTopIso R L q A residueIso).hom.hom.hom ≫ f) ha).trans
        (congrArg (fun f => f ≫
          ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
            (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false))))) ≫
              l.geometricFamilyIso.abelian.hom)) hc))
  exact Kernel.FactorSquares.factor_iff_of_carrier_iso u
    ((C.geometricSpecialKernel R L q A residueIso ⊤ true).inclusion ≫ ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false))))) ≫
      l.geometricFamilyIso.abelian.hom))
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action 1 (labels (0, false))) hu z

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.SpecialFactor
