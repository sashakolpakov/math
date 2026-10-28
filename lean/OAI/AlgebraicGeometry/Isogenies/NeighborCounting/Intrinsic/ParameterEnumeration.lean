import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockCoordinates
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor

/-! # Parameter Enumeration -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration

noncomputable section

/-! Enumerate the literal parameter labels in NativeReductionResult.
All compact coordinates are constructed from the actual ordinary lift;
the only remaining label is its original active subgroup subspace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockCoordinates OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices

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
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
  (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})

abbrev originalNeighborProjectors := CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit
  (l.genericPolarized (L := L)).abelian (l.genericAction (L := L)) (KernelLabels.nativeKernelLabels labels)

local instance neighborProjector_group (i : Fin 3) (v : Fin (s + 1)) :
    IsMonHom (originalNeighborProjectors (L := L) j hsplit labels l i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (v, false)))

def originalNeighborRepresentation (i : Fin 3) :
    (AbelianScheme.IsogenyQuotient.Parameter.Products.Construction.blockTupleFunctor (s + 1) (Reference.ParameterSubspaces.originalChoiceFunctor (A := (l.genericPolarized (L := L)).abelian.scheme)
      q (O.compact x) i
      (originalNeighborProjectors (L := L) j hsplit labels l i))).RepresentableBy
      (HeckeEvaluation.nativeNeighborParameter (l.genericPolarized (L := L)).abelian q (0 : Fin (s + 1))
        (show Fin (s + 1) → Bool from Fin.cases false (O.compact x))
        (originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient i).parameter :=
  ChoiceFunctor.nativeChoiceRepresentation (l.genericPolarized (L := L)).abelian q (O.compact x)
    (originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient i

include hTorsionQuotient in
omit [IsGalois ℚ E] [IsFractionRing R L] in
theorem originalNeighborBlockGeometry (i : Fin 3) (v : Fin (s + 1)) :
    IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i)
      (originalNeighborProjectors (L := L) j hsplit labels l i v)).hom ∧
    Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i)
      (originalNeighborProjectors (L := L) j hsplit labels l i v)).hom :=
  AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock_finite_etale (q ^ HeckeExponents.neighborLevel i) _
    (AbelianScheme.IsogenyQuotient.Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := (l.genericPolarized (L := L)).abelian.scheme)
      (𝟙 (Spec (.of L))) (q ^ HeckeExponents.neighborLevel i) (pow_pos (Fact.out : q.Prime).pos _) hTorsionQuotient)

variable (d : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
  (HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q 0
    (Fin.cases false (O.compact x)) (originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient))
  (i : Fin 3) (k : Type) [Field k] [IsAlgClosed k] (φ : d.carrier →+* k)

abbrev originalNeighborGeometricBase := (d.family (some i)).extendedParameterBase k φ

def nativeCompactCoordinates (v : Fin s) :
    Additive (originalNeighborGeometricBase j hsplit labels O l hTorsionQuotient d i k φ ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i)
        (originalNeighborProjectors (L := L) j hsplit labels l i v.succ)) ≃+
      (Fin 3 → ZMod (q ^ HeckeExponents.neighborLevel i)) :=
  Lifted.BlockCoordinates.liftedNativeBlockCoordinates j hsplit labels O l hTorsionQuotient (HeckeExponents.neighborLevel i) v.succ k
    (originalNeighborGeometricBase j hsplit labels O l hTorsionQuotient d i k φ).hom

def nativeParameterSubspaceEquiv : ULift (Fin (d.count (some i))) ≃
    {V : Submodule (ZMod q) (ActiveTorsionChoices.killedSubgroup q
      (Additive (originalNeighborGeometricBase j hsplit labels O l hTorsionQuotient d i k φ ⟶
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (originalNeighborProjectors (L := L) j hsplit labels l i 0)))) //
      Module.finrank (ZMod q) V = HeckeExponents.neighborLevel i} :=
  ChoiceFunctor.nativeEvaluatedSubspaceEquiv (l.genericPolarized (L := L)).abelian
    q (O.compact x) (originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient i
    (d.family (some i)) k φ (nativeCompactCoordinates j hsplit labels O l hTorsionQuotient d i k φ)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration
