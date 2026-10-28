import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockPointComparison

/-! # Source Group Iso -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso

noncomputable section

/-! The ambient source comparison uses the same actual scalar towers
and polarized evaluation isomorphism as the native block comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockGroupComparison

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

def evaluatedLiftSourceGroupIso :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier)))).mapGrp.obj
      (Grp.mk l.polarized.abelian.scheme) ≅
    Grp.mk (l.overEvaluationDVR v).polarized.abelian.scheme := by
  let e := l.evaluationActionIso v
  have : IsMonHom e.polarized.abelian.hom := e.polarized.abelianGroup
  exact Grp.mkIso' e.polarized.abelian

def evaluatedLiftGenericSourceGroupIso :=
  BlockGroupComparison.evaluatedIntegralBlockGroupIso R F L (Grp.mk l.polarized.abelian.scheme) v ≪≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).mapGrp.mapIso
      (evaluatedLiftSourceGroupIso l v)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso
