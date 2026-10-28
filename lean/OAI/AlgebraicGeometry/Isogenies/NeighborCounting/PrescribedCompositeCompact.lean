import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CompactType
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedCompositePointIsogeny
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OneStepKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompositeCompactPowers
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EquivariantCompact
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedPointIsogeny
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification

/-! # Prescribed Composite Compact -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedCompositeCompact

noncomputable section

/-! The independent X quotient and the actual native Frobenius have
the same full kernel. Their constructed full PEL quotient isomorphism
supplies the actual Frobenius comparison for the mixed operators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.FrobeniusComparison.X
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELTargetComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  (C0 : D.CompactKernelPrescription j iota hsplit labels)
  {x y : D.OrdinaryPoint}
  (QX : D.PrescribedOrdinaryQuotient x q (D.prescribedFullXKernel j iota hsplit labels O C0 x) y)
  (hFrob : ∀ (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
    D.prescribedFullXKernel j iota hsplit labels O C0 x T a ↔ D.relativeFrobeniusKernelCondition x T a)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CompactType.X OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedPointIsogeny
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedCompositePointIsogeny OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OneStepKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompositeCompactPowers

variable (hC0 : D.CompactKernelCondition j iota hsplit labels O C0)
  {z : D.OrdinaryPoint} {m : ℕ}
  (H0 : AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (D.pointDatum y.val).data.polarized
      (D.pointDatum y.val).data.action (labels (0, false)) m))
  (QY : D.PrescribedOrdinaryQuotient y (q ^ m)
    (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit (D.pointDatum y.val).data.polarized
      (D.pointDatum y.val).data.action m (s + 1) labels (Fin.cases H0 (C0 y m))) z)

include hC0 hFrob in
theorem prescribedComposite_compact_kernel (v : Fin s)
    (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme)
    (ha : a ≫ (D.pointDatum x.val).data.action.map
      (j.projector iota hsplit (m + 1) (labels (v.succ, false))) = a) :
    a ≫ (PrescribedCompositePointIsogeny.prescribedCompositePointIsogeny QX QY).isogeny.hom = 1 ↔
      if O.compact x v then a ^ (q ^ (m + 1)) = 1 else a = 1 := by
  let f := PrescribedPointIsogeny.prescribedPointIsogeny QX
  let g := PrescribedPointIsogeny.prescribedPointIsogeny QY
  let r := j.projector iota hsplit (m + 1) (labels (v.succ, false))
  have hsquare : (D.pointDatum x.val).data.action.map r ≫ f.isogeny.hom =
      f.isogeny.hom ≫ (D.pointDatum y.val).data.action.map r := by
    have h := f.equivariant r
    rw [Intrinsic.QuotientTargets.geometricFamily_action, Intrinsic.QuotientTargets.geometricFamily_action] at h
    exact h
  have hflags := Canonical.CompactType.X.canonicalX_compact_type j hsplit labels O C0 QX hFrob v
  have hfirst := Canonical.OneStepKernel.canonical_one_step_compact_chosen j iota hsplit
    (D.pointDatum x.val).data.polarized (D.pointDatum x.val).data.action 1 s labels (O.compact x)
    (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (O.splitting x 1 0)) (C0 x 1) (hC0 x 1)
    f.isogeny.hom (PrescribedPointIsogeny.prescribedPointIsogeny_kernel_iff QX) (Nat.succ_le_succ (Nat.zero_le m)) v
  have hsecond := Canonical.OneStepKernel.canonical_one_step_compact_chosen j iota hsplit
    (D.pointDatum y.val).data.polarized (D.pointDatum y.val).data.action m s labels (O.compact y)
    H0 (C0 y m) (hC0 y m) g.isogeny.hom (PrescribedPointIsogeny.prescribedPointIsogeny_kernel_iff QY) (Nat.le_succ m) v
  have hc := @CompositeCompactPowers.composite_compact_kernel (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)))
    (D.pointDatum x.val).data.polarized.abelian.scheme
    (D.pointDatum y.val).data.polarized.abelian.scheme
    (D.pointDatum z.val).data.polarized.abelian.scheme
    (D.pointDatum x.val).data.polarized.abelian.group
    (D.pointDatum y.val).data.polarized.abelian.group
    (D.pointDatum z.val).data.polarized.abelian.group
    f.isogeny.hom f.isogeny.preservesGroup g.isogeny.hom
    ((D.pointDatum x.val).data.action.map r) ((D.pointDatum x.val).data.action.preservesGroup r)
    ((D.pointDatum y.val).data.action.map r)
    hsquare (q ^ 1) (q ^ m) (O.compact x v) hfirst
    (fun U b hb => by
      rw [← hflags]
      exact hsecond U b hb) T a ha
  have he := Iff.of_eq (congrArg (fun u => a ≫ u = 1) (PrescribedCompositePointIsogeny.prescribedCompositePointIsogeny_hom QX QY))
  have hp : q ^ m * q ^ 1 = q ^ (m + 1) :=
    (congrArg (fun n => q ^ m * n) (pow_one q)).trans (Nat.pow_succ q m).symm
  exact he.trans (hc.trans (Iff.of_eq
    (congrArg (fun n => if O.compact x v then a ^ n = 1 else a = 1) hp)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedCompositeCompact
