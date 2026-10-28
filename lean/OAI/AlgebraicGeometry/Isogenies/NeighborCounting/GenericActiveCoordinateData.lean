import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericActiveKernel

/-! # Generic Active Coordinate Data -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericActiveCoordinateData

noncomputable section

/-! Share the actual linear coordinates, constructed generic kernels,
and their proved membership formula through one coherent record. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericActiveKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

structure ActiveCoordinateData {S : Scheme} {L : Type} [Field L]
    (f : Spec (.of L) ⟶ S) (G : Grp (Over S)) [IsCommMonObj G.X]
    (q : ℕ) [Module (ZMod q) (Additive (Over.mk f ⟶ G.X))] where
  coordinates : Additive (Over.mk f ⟶ G.X) ≃ₗ[ZMod q] ((Fin 2 → ZMod q) × ZMod q)
  kernel : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q) →
    Kernel.Properties.FiniteFlatKernel ((Over.pullback f).obj G.X)
  membership : ∀ J a, coordinates a ∈ J ↔
    ∃ b : Over.mk (𝟙 (Spec (.of L))) ⟶ (kernel J).carrier,
      b ≫ (kernel J).inclusion = GroupPointBaseChange.pointPullbackGroupEquiv f G a.toMul

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

def evaluatedActiveCoordinateData :
    ActiveCoordinateData (Spec.map (CommRingCat.ofHom (algebraMap F L)))
      (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q
        ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
          (j.projector iota hsplit 1 (labels (0, false)))))) q where
  coordinates := Evaluated.ActiveCoordinateEquiv.evaluatedActivePointLinearEquiv j hsplit labels O l v eA
  kernel := Evaluated.GenericActiveKernel.evaluatedGenericActiveKernel j hsplit labels O l v eA
  membership := Evaluated.GenericActiveKernel.evaluatedGenericActiveKernel_membership j hsplit labels O l v eA

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericActiveCoordinateData
