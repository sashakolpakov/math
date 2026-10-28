import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Targets
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso

/-! # Classified Field Target -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ClassifiedFieldTarget

noncomputable section

/-! The given fine-moduli property classifies the constructed positive
integral PEL object over the evaluation field. The actual target and
its full data comparison are outputs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Targets.Lifts

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q)
variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
variable (b : B.R →+* R)

variable (hgood : D.IsGoodCompletelySplitReduction)
  (c : Spec (.of L) ⟶ B.base)
  (hc : c = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ Lifts.dvrBase R b)
  (A : PELModuli.IntegralModel.PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N
    (Over.mk c))

local instance fieldTargetReduced : IsReduced (Over.mk c).left :=
  inferInstanceAs (IsReduced (Spec (.of L)))

def classifiedFieldTarget : Evaluated.Targets.Lifts.EvaluatedTarget D R L b where
  map := (hgood _ A).choose.left
  overBase := (hgood _ A).choose.w.trans hc

def classifiedFieldTargetDataIso :
    PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
      (D.integral.universal.data.pullback (classifiedFieldTarget D R L b hgood c hc A).map) A.data :=
  (Classical.choice (hgood _ A).choose_spec.1).toActionIso.trans
    (PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackId A.data)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ClassifiedFieldTarget
