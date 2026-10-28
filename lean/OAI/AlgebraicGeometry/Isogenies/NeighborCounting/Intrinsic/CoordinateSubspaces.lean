import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.EvaluatedSubspaces
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateEnumeration
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.CoordinateSubspaces
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.CoordinateData
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.KernelParameters
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.RationalMembership
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateMapValues

/-! # Coordinate Subspaces -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoordinateSubspaces

/-! The complete original parameter labels enumerate active subspaces
over their actual common evaluation field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveSubspaces
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.EvaluatedSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces

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
  (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

local instance neighborProjector_group (i : Fin 3) (v : Fin (s + 1)) :
    IsMonHom (ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (v, false)))

variable (d : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
  (HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q 0
    (Fin.cases false (O.compact x)) (ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient))
  (i : Fin 3) (k : Type) [Field k] [IsAlgClosed k] (φ : d.carrier →+* k)

def nativeParameterCoordinateData
    (c : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))) ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.genericAction (L := L)).map (j.projector iota hsplit 1 (labels (0, false))))) ≃+
        ((Fin 2 → ZMod q) × ZMod q)) :=
  Joint.CoordinateData.jointCoordinateData j iota hsplit
    (l.genericPolarized (L := L)).abelian (l.genericAction (L := L)) (O.compact x)
    (ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient d i k φ (labels (0, false)) rfl
    (ParameterEnumeration.nativeCompactCoordinates j hsplit labels O l hTorsionQuotient d i k φ) c

def nativeCoordinateKernelParameters
    (C : GenericActiveCoordinateData.ActiveCoordinateData
      (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier)))
      (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.genericAction (L := L)).map
        (j.projector iota hsplit 1 (labels (0, false)))))) q) :=
  Joint.KernelParameters.jointKernelParameters j iota hsplit
    (l.genericPolarized (L := L)).abelian (l.genericAction (L := L)) (O.compact x)
    (ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient d i k φ (labels (0, false)) rfl
    (ParameterEnumeration.nativeCompactCoordinates j hsplit labels O l hTorsionQuotient d i k φ) C

def nativeParameterCoordinateSubspaceEquiv
    (c : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))) ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.genericAction (L := L)).map (j.projector iota hsplit 1 (labels (0, false))))) ≃+
        ((Fin 2 → ZMod q) × ZMod q)) :
    ULift (Fin (d.count (some i))) ≃
      {J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q) //
        Module.finrank (ZMod q) J = HeckeExponents.neighborLevel i} :=
  (nativeParameterCoordinateData j hsplit labels O l hTorsionQuotient d i k φ c).val

end AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoordinateSubspaces

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoordinateSubspaces.IntrinsicRationalMembership

/-! The actual original PEL parameter has the prescribed coordinate
subspace over its common evaluation field, before geometric extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveSubspaces
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.EvaluatedSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage.Prime

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
  (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

local instance neighborProjector_group (i : Fin 3) (v : Fin (s + 1)) :
    IsMonHom (ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (v, false)))

variable (d : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
  (HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q 0
    (Fin.cases false (O.compact x)) (ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient))
  (i : Fin 3) (k : Type) [Field k] [IsAlgClosed k] (φ : d.carrier →+* k)

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (v : Fin (s + 1)) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false (O.compact x)) i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i)
    (HeckeExponents.neighborExponents 0 (Fin.cases false (O.compact x)) i v)
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false (O.compact x)) i v)

variable
  (c : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))) ⟶
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.genericAction (L := L)).map (j.projector iota hsplit 1 (labels (0, false))))) ≃+
      ((Fin 2 → ZMod q) × ZMod q))
  (a : ULift (Fin (d.count (some i))))
  (z : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))) ⟶
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.genericAction (L := L)).map (j.projector iota hsplit 1 (labels (0, false))))))

omit [IsFractionRing R L] in
theorem nativeParameterCoordinateSubspaceEquiv_rational_membership :
    c z ∈ (nativeParameterCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient d i k φ c a).val ↔
    z.toMul ∈ (Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveSubgroup j iota hsplit
      (l.genericPolarized (L := L)).abelian (l.genericAction (L := L)) (O.compact x)
      (ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient d i (labels (0, false)) a).points
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier)))) (𝟙 _) := by
  exact (nativeParameterCoordinateData j hsplit labels O l hTorsionQuotient d i k φ c).property.2 a z

end AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoordinateSubspaces.IntrinsicRationalMembership

end

end OAI
