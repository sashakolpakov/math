import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotientKernel

/-! # Integral Kernel Presentation -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralKernelPresentation

noncomputable section

/-! Name the genuine original integral kernel inclusion and its
all-test prescribed-kernel proof before specializing the quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralActiveKernels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotients OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalQuotientKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotientKernel

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

local instance neighborProjector_group (i : Fin 3) (v : Fin (s + 1)) :
    IsMonHom (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (v, false)))

variable (a : ConstructedActiveEvaluation.LiftedActiveEvaluation (L := L) j hsplit labels O l hTorsionQuotient)

variable (hlabels : ∀ v : Fin (s + 1),
  labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
  (i : Fin 3) (p : ULift (Fin (a.evaluation.count (some i))))

private def morphismDomain {C : Type*} [Category C] {X Y : C} (_f : X ⟶ Y) : C := X

def originalIntegralKernelCarrier :
    letI := a.evaluation.scalarAlgebra R
    letI := a.evaluation.scalarTower R
    let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
    Over (Spec (.of v.carrier)) :=
  morphismDomain (IntegralQuotients.originalIntegralQuotient j hsplit labels O l hTorsionQuotient a hlabels i p).identitySourceInclusion

def originalIntegralKernelInclusion :
    letI := a.evaluation.scalarAlgebra R
    letI := a.evaluation.scalarTower R
    let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
    originalIntegralKernelCarrier j hsplit labels O l hTorsionQuotient a hlabels i p ⟶
      (l.overEvaluationDVR v).polarized.abelian.scheme :=
  (IntegralQuotients.originalIntegralQuotient j hsplit labels O l hTorsionQuotient a hlabels i p).identitySourceInclusion

theorem originalIntegralPrescribedKernel :
    letI := a.evaluation.scalarAlgebra R
    letI := a.evaluation.scalarTower R
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (IntegralQuotientKernel.originalIntegralModelIsogeny j hsplit labels O l hTorsionQuotient a hlabels i p).hom
      (originalIntegralKernelInclusion j hsplit labels O l hTorsionQuotient a hlabels i p) :=
  (IntegralQuotients.originalIntegralQuotient j hsplit labels O l hTorsionQuotient a hlabels i p).identitySourceIsogeny_kernel

theorem originalIntegralKernelBound :
    letI := a.evaluation.scalarAlgebra R
    letI := a.evaluation.scalarTower R
    let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
    ∀ (T : Over (Spec (.of v.carrier))) (z : T ⟶ (l.overEvaluationDVR v).polarized.abelian.scheme),
      z ≫ (IntegralQuotientKernel.originalIntegralModelIsogeny j hsplit labels O l hTorsionQuotient a hlabels i p).hom = 1 →
        z ^ (q ^ HeckeExponents.neighborLevel i) = 1 :=
  (IntegralQuotients.originalIntegralQuotient j hsplit labels O l hTorsionQuotient a hlabels i p).identitySourceIsogeny_kernel_bound

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralKernelPresentation
