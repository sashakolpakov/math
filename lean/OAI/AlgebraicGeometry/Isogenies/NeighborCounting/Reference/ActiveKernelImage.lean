import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveKernelComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.ActiveKernelImage

/-! # Active Kernel Image -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveKernelImage

noncomputable section

/-! Identify the constructed generic active-kernel image with the unchanged original active choice in the abelian source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GenericActiveKernels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage.Prime OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoordinateSubspaces.IntrinsicRationalMembership
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrimeBlockSplitting OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitKernelParameterComparison
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

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

variable (i : Fin 3) (p : ULift (Fin (a.evaluation.count (some i))))

/-- The inclusion into the actual abelian source retains the original parameter's active choice. -/
def originalActiveKernelImageIdentity :=
  let C := CoordinateSubspaces.originalEvaluatedCoordinateData j hsplit labels O l hTorsionQuotient a
  let f := Spec.map (CommRingCat.ofHom (algebraMap L a.evaluation.carrier))
  let p₁ := (l.genericAction (L := L)).map (j.projector iota hsplit 1 (labels (0, false)))
  let e := PrimeBlockSplitting.primeBlockSplitIso q p₁ f a.blockIso
  PLift.up (Joint.ActiveKernelImage.jointActiveKernel_image_eq j iota hsplit
    (l.genericPolarized (L := L)).abelian (l.genericAction (L := L)) (O.compact x)
    (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient a.evaluation i
    (AlgebraicClosure a.evaluation.carrier)
    (algebraMap a.evaluation.carrier (AlgebraicClosure a.evaluation.carrier))
    (labels (0, false)) rfl
    (Intrinsic.ParameterEnumeration.nativeCompactCoordinates j hsplit labels O l hTorsionQuotient a.evaluation i
      (AlgebraicClosure a.evaluation.carrier)
      (algebraMap a.evaluation.carrier (AlgebraicClosure a.evaluation.carrier))) C e p)

theorem originalActiveKernel_image_eq :
    type_of% (originalActiveKernelImageIdentity j hsplit labels O l hTorsionQuotient a i p).down :=
  (originalActiveKernelImageIdentity j hsplit labels O l hTorsionQuotient a i p).down

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveKernelImage
