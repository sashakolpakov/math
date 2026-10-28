import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedTowerIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedIsoCanonicalPairing

/-! # Pairing Source Maps -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps.PolarizedIso

/-! The actual generic source comparison preserves its positive
polarization, normalized Poincare data, and every ordered level marking.
Its underlying map is the one used in the original active-kernel transport. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockGroupComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedTowerIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedIsoCanonicalPairing

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x) (v : EvaluationDVRLifts.EvaluationDVR R L)

def evaluatedLiftGenericPolarizedIso :=
  (PolarizedTowerIso.evaluatedIntegralPolarizedIso R F L l.polarized v).trans
    ((l.evaluationActionIso v).polarized.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))))

theorem evaluatedLiftGenericPolarizedIso_group_hom :
    (evaluatedLiftGenericPolarizedIso (F := F) l v).abelian.hom =
      (SourceGroupIso.evaluatedLiftGenericSourceGroupIso (F := F) l v).hom.hom.hom := by
  change (PolarizedTowerIso.evaluatedIntegralPolarizedIso R F L l.polarized v).abelian.hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).map
        (l.evaluationActionIso v).polarized.abelian.hom =
    (BlockGroupComparison.evaluatedIntegralBlockGroupIso R F L (Grp.mk l.polarized.abelian.scheme) v).hom.hom.hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).map
        (SourceGroupIso.evaluatedLiftSourceGroupIso l v).hom.hom.hom
  exact congrArg (fun f => f ≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).map
      (l.evaluationActionIso v).polarized.abelian.hom)
    (PolarizedTowerIso.evaluatedIntegralPolarizedIso_group_hom R F L l.polarized v)

def evaluatedLiftGenericPairingIdentity (n : ℕ) (hn : 0 < n) :=
  PLift.up (PolarizedIsoCanonicalPairing.polarizedIso_canonical_pairing (evaluatedLiftGenericPolarizedIso (F := F) l v) n hn)

theorem evaluatedLiftGenericPolarizedIso_canonical_pairing (n : ℕ) (hn : 0 < n) :
    type_of% (evaluatedLiftGenericPairingIdentity (F := F) l v n hn).down :=
  (evaluatedLiftGenericPairingIdentity (F := F) l v n hn).down

end AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps.PolarizedIso

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps

/-! Explicit source endpoints for the actual polarized isomorphism and ambient group map used by the evaluated block pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockGroupComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedTowerIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedIsoCanonicalPairing

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x) (v : EvaluationDVRLifts.EvaluationDVR R L)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps.PolarizedIso

def evaluatedPairingSourceIso :
    AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
      ((l.polarized.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).pullback
        (Spec.map (CommRingCat.ofHom (algebraMap F L))))
      ((l.overEvaluationDVR v).polarized.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))) :=
  PolarizedIso.evaluatedLiftGenericPolarizedIso (F := F) l v

def evaluatedPairingSourceMap :
    ((l.polarized.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).pullback
      (Spec.map (CommRingCat.ofHom (algebraMap F L)))).abelian.scheme ⟶
    ((l.overEvaluationDVR v).polarized.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).abelian.scheme :=
  (SourceGroupIso.evaluatedLiftGenericSourceGroupIso (F := F) l v).hom.hom.hom

theorem evaluatedPairingSourceMap_eq :
    (evaluatedPairingSourceIso (F := F) l v).abelian.hom = evaluatedPairingSourceMap (F := F) l v :=
  PolarizedIso.evaluatedLiftGenericPolarizedIso_group_hom (F := F) l v

end AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps

end

end OAI
