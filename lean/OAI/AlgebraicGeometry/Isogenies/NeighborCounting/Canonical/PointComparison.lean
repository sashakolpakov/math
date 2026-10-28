import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification

/-! # Point Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PointComparison

noncomputable section

/-! An actual marked special PEL isogeny with the independently
prescribed complete kernel has the canonical native quotient point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}

variable {x y : D.OrdinaryPoint} {z : D.GeometricPoint} {n : ℕ}
  {kernel : ∀ (T : Over D.integralGeometricBase.left),
    (T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) → Prop}
  (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x.val))
    (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum z)) n)
  (hf : ∀ (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
    a ≫ f.isogeny.hom = 1 ↔ kernel T a)

include hf in
theorem point_eq_of_prescribed_kernel (hgood : D.IsGoodCompletelySplitReduction)
    (Q : D.PrescribedOrdinaryQuotient x n kernel y) : z = y.val := by
  have : IsClosedImmersion Q.inclusion.left := Q.closed
  have : Mono Q.inclusion := Over.mono_of_mono_left _
  have hk : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f.isogeny.hom Q.inclusion := by
    intro T a
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := (Q.realizes T a).mpr ((hf T a).mp ha)
      exact ⟨b, hb, fun c hc => (cancel_mono Q.inclusion).mp (hc.trans hb.symm)⟩
    · intro ha
      exact (hf T a).mpr ((Q.realizes T a).mp ha.exists)
  exact (PointQuotientWitness.independentQuotient_point hgood z f hk Q.quotient).symm.trans
    (D.pointOfPEL_eq_of_classifies hgood Q.quotient.target y.val Q.classifies)

include hf in
theorem point_eq_of_canonical_kernel (hgood : D.IsGoodCompletelySplitReduction)
    (hy : D.CanonicalOrdinaryQuotient x n kernel y) : z = y.val := by
  obtain ⟨Q⟩ := hy.1
  exact point_eq_of_prescribed_kernel f hf hgood Q

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PointComparison
