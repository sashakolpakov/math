import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.KernelMembership
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedGenericKernel

/-! # Generic Active Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericActiveKernel

noncomputable section

/-! The integral ordinary active kernel gives an actual finite flat
kernel in the original generic q-block. Its points are precisely the
prescribed standard subspace in the constructed coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.KernelMembership
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedGenericKernel
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

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

def evaluatedGenericActiveKernel :
    Kernel.Properties.FiniteFlatKernel ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
        (j.projector iota hsplit 1 (labels (0, false)))))) :=
  TransportedGenericKernel.transportedGenericKernel (Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))) _ _
    (PrimeBlockComparison.evaluatedPrimeBlockGroupIso (F := F) j hsplit l v (labels (0, false)))
    (ActiveCoordinateEquiv.evaluatedActiveIntegralKernel j hsplit labels O l v eA J)

theorem evaluatedGenericActiveKernel_membership
    (a : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L))) ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
        (j.projector iota hsplit 1 (labels (0, false)))))) :
    ActiveCoordinateEquiv.evaluatedActivePointLinearEquiv j hsplit labels O l v eA a ∈ J ↔
      ∃ b : Over.mk (𝟙 (Spec (.of L))) ⟶
          (evaluatedGenericActiveKernel j hsplit labels O l v eA J).carrier,
        b ≫ (evaluatedGenericActiveKernel j hsplit labels O l v eA J).inclusion =
          GroupPointBaseChange.pointPullbackGroupEquiv (Spec.map (CommRingCat.ofHom (algebraMap F L)))
            (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q
              ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
                (j.projector iota hsplit 1 (labels (0, false)))))) a.toMul := by
  have ht := TransportedGenericKernel.transportedGenericKernel_membership
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))) _ _
    (PrimeBlockComparison.evaluatedPrimeBlockGroupIso (F := F) j hsplit l v (labels (0, false)))
    (ActiveCoordinateEquiv.evaluatedActiveIntegralKernel j hsplit labels O l v eA J) a.toMul
  rw [PrimeBlockComparison.evaluatedActivePrimeBlockGroupIso_points] at ht
  exact (KernelMembership.evaluatedActiveKernel_membership j hsplit labels O l v eA J a).trans ht.symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericActiveKernel
