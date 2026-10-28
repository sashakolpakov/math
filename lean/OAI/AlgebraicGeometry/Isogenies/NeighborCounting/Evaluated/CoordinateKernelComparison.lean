import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.KernelComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveParameterFamily
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EmbeddedActiveFamilies
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels

/-! # Coordinate Kernel Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.CoordinateKernelComparison

noncomputable section

/-! Transport the full kernel at the actual evaluated coordinate family before original-parameter specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericActiveKernel
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockInclusion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedKernelParameterFamily.Family
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockInclusion.Square
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

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EmbeddedActiveFamilies OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveParameterFamily.SourceFamilies
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.KernelComparison

private theorem equalityAt (T : Type*) {x y : T} (h : x = y) : x = y := h

def evaluatedCoordinateFullKernelComparison (n : ℕ) (c : Fin (s + 1) → Bool)
    (F₀ : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup
      (l.polarized.abelian.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).scheme
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L))))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap F L))
  let g := Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))
  let F₁ := EmbeddedActiveFamilies.embeddedActiveFamily (P := Over.mk g) (q ^ 1)
    ((l.overEvaluationDVR v).action.map (j.projector iota hsplit 1 (labels (0, false))))
    (ActiveCoordinateEquiv.evaluatedActiveIntegralKernel j hsplit labels O l v eA J)
  let comparison := (KernelComparison.evaluatedFullKernelComparisonFromActive (F := F) j hsplit l v
    n (Intrinsic.KernelLabels.nativeKernelLabels labels) 0 c F₀ F₁).down
  exact PLift.up (fun h : ActiveParameterFamily.SourceFamilies.evaluatedIntegralActiveSourceFamily j hsplit labels O l v eA J =
      AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter
        (Grp.mk (l.polarized.abelian.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).scheme)
        (Over.mk f) F₀ => equalityAt
          (AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup (ActiveParameterFamily.SourceFamilies.evaluatedOriginalAmbientGroup (F := F) (L := L) l).X
            (Over.mk (𝟙 (Spec (.of L))))) (comparison h))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.CoordinateKernelComparison
