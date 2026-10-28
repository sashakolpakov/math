import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ChosenPointComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OneStepKernel

/-! # Active Compact Point -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ActiveCompactPoint

noncomputable section

/-! Active and compact chosen-component computations determine the
independent canonical quotient point. The complete opposite kernel is
derived from the actual positive PEL isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ChosenPointComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OneStepKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedMapKernel

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (hlabels : ∀ v : Fin (s + 1), labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  (C0 : D.CompactKernelPrescription j iota hsplit labels)
  (hC0 : D.CompactKernelCondition j iota hsplit labels O C0)
  {x y : D.OrdinaryPoint} {z : D.GeometricPoint} (n : ℕ)
  (H0 : AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (D.pointDatum x.val).data.polarized
      (D.pointDatum x.val).data.action (labels (0, false)) n))
  (Q : D.PrescribedOrdinaryQuotient x (q ^ n)
    (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit (D.pointDatum x.val).data.polarized
      (D.pointDatum x.val).data.action n (s + 1) labels (Fin.cases H0 (C0 x n))) y)
  (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x.val)) (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum z)) (q ^ n))
  (hfbound : ∀ (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
    a ≫ f.isogeny.hom = 1 → a ^ (q ^ n) = 1)
  (hfactive : ∀ (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
    a ≫ (D.pointDatum x.val).data.action.map (j.projector iota hsplit n (labels (0, false))) = a →
      (a ≫ f.isogeny.hom = 1 ↔ ∃ h : T ⟶ H0.group.X,
        h ≫ H0.inclusion.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit
          (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action n
            (labels (0, false)) = a))
  (hfcompact : ∀ (v : Fin s) (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
    a ≫ (D.pointDatum x.val).data.action.map (j.projector iota hsplit n (labels (v.succ, false))) = a →
      (a ≫ f.isogeny.hom = 1 ↔ if O.compact x v then a ^ (q ^ n) = 1 else a = 1))

include Q hlabels hC0 hfbound hfactive hfcompact in
theorem point_eq_of_active_and_compact (hgood : D.IsGoodCompletelySplitReduction) : z = y.val := by
  let A := (D.pointDatum x.val).data.polarized
  let ρ := (D.pointDatum x.val).data.action
  let g := Intrinsic.QuotientTargets.witnessIsogeny Q.quotient
  let H : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n) :=
    Fin.cases H0 (C0 x n)
  apply ChosenPointComparison.point_eq_of_prescribed_chosen j hsplit labels hlabels n H Q f hfbound ?_ hgood
  intro v T a ha
  cases v using Fin.cases with
  | zero => exact hfactive T a ha
  | succ w =>
    have hg := PrescribedMapKernel.prescribed_quotient_kernel_iff D Q
    have hc := OneStepKernel.canonical_one_step_compact_chosen j iota hsplit A ρ n s labels (O.compact x)
      H0 (C0 x n) (hC0 x n) g.isogeny.hom hg (Nat.le_refl n) w T a ha
    have hq : a ≫ g.isogeny.hom = 1 ↔ ∃ h : T ⟶ (C0 x n w).group.X,
        h ≫ (C0 x n w).inclusion.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n
          (labels (w.succ, false)) = a := by
      constructor
      · exact PrescribedMapKernel.prescribed_map_chosen_factor j iota hsplit A ρ n (s + 1) labels H
          g.isogeny.hom hg (Nat.le_refl n) w.succ T a ha
      · rintro ⟨h, rfl⟩
        exact PrescribedMapKernel.prescribed_map_chosen_killed j iota hsplit A ρ n (s + 1) labels H
          g.isogeny.hom hg w.succ T h
    exact (hfcompact w T a ha).trans (hc.symm.trans hq)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ActiveCompactPoint
