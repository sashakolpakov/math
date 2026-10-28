import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointDataSpecialization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange

/-! # Integral PEL -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The original integral lift and its generic fiber are actual objects
of the same integral PEL moduli problem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x)

def Lifts.IntegralLift.integralObject : PELModuli.IntegralModel.PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N
    (Over.mk (Lifts.dvrBase R b)) :=
  D.integral.universal.pullback (Over.homMk l.map l.overBase)

theorem Lifts.IntegralLift.integralObject_data : l.integralObject.data = l.actionData := rfl

def Lifts.IntegralLift.genericIntegralObject : PELModuli.IntegralModel.PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ Lifts.dvrBase R b)) :=
  l.integralObject.pullback
    (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R L))) rfl)

theorem Lifts.IntegralLift.genericIntegralObject_data : (l.genericIntegralObject (L := L)).data =
    l.actionData.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L))) := rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
