import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedPointIsogeny
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CompositeBound
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELKernelTargetTransport
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedMapKernel
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification

/-! # Prescribed Composite Point Isogeny -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedCompositePointIsogeny

noncomputable section

/-! Compose the independent X quotient with a second independent
prescribed quotient, retaining the literal multiplier and full marking. -/

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

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedPointIsogeny OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CompositeBound OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Components

variable {x y z : D.OrdinaryPoint} {m : ℕ}
  {kernelX : ∀ (T : Over D.integralGeometricBase.left),
    (T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) → Prop}
  {kernelY : ∀ (T : Over D.integralGeometricBase.left),
    (T ⟶ (D.pointDatum y.val).data.polarized.abelian.scheme) → Prop}
  (QX : D.PrescribedOrdinaryQuotient x q kernelX y)
  (QY : D.PrescribedOrdinaryQuotient y (q ^ m) kernelY z)

def prescribedCompositePointIsogeny :
    AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x.val))
      (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum z.val)) (q ^ (m + 1)) :=
  ((PrescribedPointIsogeny.prescribedPointIsogeny QX).comp (PrescribedPointIsogeny.prescribedPointIsogeny QY)).castMultiplier
    ((Nat.mul_comm q (q ^ m)).trans (Nat.pow_succ q m).symm)

theorem prescribedCompositePointIsogeny_hom :
    (prescribedCompositePointIsogeny QX QY).isogeny.hom =
      (PrescribedPointIsogeny.prescribedPointIsogeny QX).isogeny.hom ≫
        (PrescribedPointIsogeny.prescribedPointIsogeny QY).isogeny.hom := by
  rw [prescribedCompositePointIsogeny, AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.castMultiplier_hom]
  rfl

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (HX : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (D.pointDatum x.val).data.polarized
      (D.pointDatum x.val).data.action (labels (v, false)) 1))
  (HY : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (D.pointDatum y.val).data.polarized
      (D.pointDatum y.val).data.action (labels (v, false)) m))

theorem prescribedCompositePointIsogeny_kernel_bound
    (QX : D.PrescribedOrdinaryQuotient x q
      (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action 1 (s + 1) labels HX) y)
    (QY : D.PrescribedOrdinaryQuotient y (q ^ m)
      (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit (D.pointDatum y.val).data.polarized
        (D.pointDatum y.val).data.action m (s + 1) labels HY) z)
    (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme)
    (ha : a ≫ (prescribedCompositePointIsogeny QX QY).isogeny.hom = 1) :
    a ^ (q ^ (m + 1)) = 1 := by
  let f := PrescribedPointIsogeny.prescribedPointIsogeny QX
  let g := PrescribedPointIsogeny.prescribedPointIsogeny QY
  have hf : ∀ (U : Over D.integralGeometricBase.left)
      (b : U ⟶ (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x.val)).abelian.scheme),
      b ≫ f.isogeny.hom = 1 → b ^ q = 1 := by
    intro U b hb
    have h := PrescribedKernelOf.Components.prescribed_full_kernel_killed j iota hsplit
      (D.pointDatum x.val).data.polarized (D.pointDatum x.val).data.action 1 (s + 1) labels HX U b
      ((PrescribedPointIsogeny.prescribedPointIsogeny_kernel_iff QX U b).mp hb)
    exact (congrArg (fun n => b ^ n) (pow_one q)).symm.trans h
  have h := Canonical.CompositeBound.composite_kernel_bound f.isogeny.hom g.isogeny.hom q (q ^ m) hf
    (fun U b hb => PrescribedKernelOf.Components.prescribed_full_kernel_killed j iota hsplit
      (D.pointDatum y.val).data.polarized (D.pointDatum y.val).data.action m (s + 1) labels HY U b
      ((PrescribedPointIsogeny.prescribedPointIsogeny_kernel_iff QY U b).mp hb)) T a
    ((congrArg (fun u => a ≫ u) (prescribedCompositePointIsogeny_hom QX QY)).symm.trans ha)
  exact (congrArg (fun n => a ^ n) (Nat.pow_succ q m)).trans h

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedCompositePointIsogeny
