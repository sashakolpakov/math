import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.ImageMembership
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockPointComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces

/-! # Kernel Membership -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.KernelMembership

noncomputable section

/-! Identify the constructed integral active kernel on the original
evaluation-field points using the actual evaluated source comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVROrdinaryCoordinates.Ordinary OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockPointComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTypedSubspaces
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv

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
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L]
  [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
  (v : EvaluationDVRLifts.EvaluationDVR R L)
  {I : Type} [Finite I]
  (eA : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) (((l.action).pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
          (j.projector iota hsplit 1 (labels (0, false))))))

variable (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q))
  (a : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L))) ⟶
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
      (j.projector iota hsplit 1 (labels (0, false))))))

theorem evaluatedActiveKernel_membership :
    ActiveCoordinateEquiv.evaluatedActivePointLinearEquiv j hsplit labels O l v eA a ∈ J ↔
      ∃ b : Sections.Lifts.genericTest v.carrier L ⟶ (ActiveCoordinateEquiv.evaluatedActiveIntegralKernel j hsplit labels O l v eA J).carrier,
        b ≫ (ActiveCoordinateEquiv.evaluatedActiveIntegralKernel j hsplit labels O l v eA J).inclusion =
          (ActiveCoordinateEquiv.evaluatedActivePointTransport (F := F) j hsplit labels l v a).toMul := by
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel j hsplit labels O l v eA
  let hk := Lifted.OrdinarySplitting.Ordinary.liftedActiveBlock_killed j hsplit labels (l.overEvaluationDVR v) (Sections.Lifts.genericTest v.carrier L)
  let := GenericPointCoordinates.Lifts.genericPointModule v.carrier L q (Lifted.OrdinarySplitting.Ordinary.liftedActiveBlock j hsplit labels (l.overEvaluationDVR v)).X hk
  have hm := OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel_linear_membership v.carrier L q
    (Lifted.OrdinarySplitting.Ordinary.liftedActiveBlock j hsplit labels (l.overEvaluationDVR v)) C hk J
    (ActiveCoordinateEquiv.evaluatedActivePointTransport (F := F) j hsplit labels l v a).toMul
  exact hm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.KernelMembership
