import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison

/-! # Point Quotient Witness -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness

noncomputable section

/-! A full PEL isogeny between the original native point data gives an
actual quotient witness and identifies its moduli point with every
independent quotient of the same complete kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.DualIdentification

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {A C : D.GeometricPELDatum} {n : ℕ}
variable {H : Grp (Over D.integralGeometricBase.left)}
variable {i : H.X ⟶ A.data.polarized.abelian.scheme}

def isogenyWitness (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily A) (Intrinsic.QuotientTargets.geometricFamily C) n)
    (hf : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f.isogeny.hom i) : D.QuotientWitness A n H i where
  target := C
  isogeny := f.isogeny
  kernel := hf
  polarization := by
    have h := f.polarization
    rw [PolarizedComparison.pel_dualMap, Intrinsic.DualIdentification.dualMap_eq_native] at h
    exact h
  action r := by
    have h := f.equivariant r
    rw [Intrinsic.QuotientTargets.geometricFamily_action, Intrinsic.QuotientTargets.geometricFamily_action] at h
    exact h
  marking T c := (f.marking T.unop c).symm

theorem independentQuotient_point (hgood : D.IsGoodCompletelySplitReduction)
    (x : D.GeometricPoint)
    (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily A) (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x)) n)
    (hf : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f.isogeny.hom i) (Q : D.QuotientWitness A n H i) :
    D.pointOfPEL hgood Q.target = x := by
  exact (Intrinsic.QuotientTargets.quotientWitness_point_eq hgood Q (isogenyWitness f hf)).trans
    (D.pointOfPEL_eq_of_pointDatumIso hgood x (D.pointDatum x)
      (PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.refl _))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness
