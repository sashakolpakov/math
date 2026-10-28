import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SupportedIntrinsicSubgroup
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericBlockInclusion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActionBlockTorsionInclusion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionBlockPairingIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingBlockIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActionPairingSource

/-! # Action Block Iso -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActionBlockIso
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open scoped _root_.CategoryTheory.Obj
section

/-! Give the actual evaluated block isomorphism the literal endpoints of the coherent action data. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Group

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SupportedIntrinsicSubgroup.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockPointComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericBlockInclusion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps.PolarizedIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActionBlockTorsionInclusion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionBlockPairingIso.Polarized OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActionPairingSource

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x) (v : EvaluationDVRLifts.EvaluationDVR R L)

abbrev evaluatedActionBlockGroupIso (n : ℕ) (τ : Gal(E/ℚ)) :=
  PairingBlockIso.evaluatedLiftGenericPairingBlockIso (F := F) j hsplit l v n τ

end Group

end

/-! Construct each original evaluated coefficient-block isomorphism together with its actual ambient inclusion square at the coherent action-source index. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SupportedIntrinsicSubgroup.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockPointComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericBlockInclusion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps.PolarizedIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActionBlockTorsionInclusion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionBlockPairingIso.Polarized OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActionPairingSource

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x) (v : EvaluationDVRLifts.EvaluationDVR R L)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActionBlockIso.Group

abbrev evaluatedActionBlockIso (n : ℕ) (τ : Gal(E/ℚ)) :=
  Group.evaluatedActionBlockGroupIso
    (F := F) j hsplit l v n τ

end AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActionBlockIso

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActionBlockIso.GenericPairing

/-! The actual evaluated source and original coefficient-block isomorphisms
identify the canonical chosen/opposite pairings on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SupportedIntrinsicSubgroup.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockPointComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericBlockInclusion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps.PolarizedIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActionBlockTorsionInclusion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionBlockPairingIso.Polarized OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActionPairingSource OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActionBlockIso

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x) (v : EvaluationDVRLifts.EvaluationDVR R L)

def evaluatedLiftGenericBlockPairingComparison (n : ℕ) (τ υ : Gal(E/ℚ)) :=
  PLift.up (ActionBlockPairingIso.Polarized.polarizedActionBlockPairing_iso
    (l.polarized.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F))))
    (l.overEvaluationDVR v).polarized
    (l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F))))
    (l.overEvaluationDVR v).action
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))
    (PairingSourceMaps.evaluatedPairingSourceIso (F := F) l v)
    (PairingSourceMaps.evaluatedPairingSourceMap (F := F) l v)
    (PairingSourceMaps.evaluatedPairingSourceMap_eq (F := F) l v)
    (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)
    (j.projector iota hsplit n τ) (j.projector iota hsplit n υ))

abbrev evaluatedPairingChosenBlock (n : ℕ) (τ υ : Gal(E/ℚ)) :=
  (evaluatedLiftGenericBlockPairingComparison (F := F) j hsplit l v n τ υ).down
    (evaluatedActionBlockIso (F := F) j hsplit l v n τ).hom

abbrev evaluatedPairingOppositeBlock (n : ℕ) (τ υ : Gal(E/ℚ)) :=
  evaluatedPairingChosenBlock (F := F) j hsplit l v n τ υ
    (evaluatedActionBlockIso (F := F) j hsplit l v n υ).hom

abbrev evaluatedPairingChosenInclusion (n : ℕ) (τ υ : Gal(E/ℚ)) :=
  evaluatedPairingOppositeBlock (F := F) j hsplit l v n τ υ
    (GenericBlockInclusion.evaluatedLiftGenericBlockGroupIso_inclusion (F := F) j hsplit l v n τ)

def evaluatedLiftGenericBlockPairingIdentity (n : ℕ) (τ υ : Gal(E/ℚ)) :=
  PLift.up (evaluatedPairingChosenInclusion (F := F) j hsplit l v n τ υ
    (GenericBlockInclusion.evaluatedLiftGenericBlockGroupIso_inclusion (F := F) j hsplit l v n υ))

theorem evaluatedLiftGenericBlockPairing (n : ℕ) (τ υ : Gal(E/ℚ)) :
    type_of% (evaluatedLiftGenericBlockPairingIdentity (F := F) j hsplit l v n τ υ).down :=
  (evaluatedLiftGenericBlockPairingIdentity (F := F) j hsplit l v n τ υ).down

end AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActionBlockIso.GenericPairing

end

end OAI
