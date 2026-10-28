import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.PELChosenComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PointComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedMapKernel

/-! # Chosen Point Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ChosenPointComparison

noncomputable section

/-! A full positive geometric PEL isogeny with the prescribed chosen
components has the independent canonical quotient point. Opposite
components follow from its actual polarization and are not assumptions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.PELChosenComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PointComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedMapKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Components

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
  {x y : D.OrdinaryPoint} {z : D.GeometricPoint} (n : ℕ)
  (H : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (D.pointDatum x.val).data.polarized
      (D.pointDatum x.val).data.action (labels (v, false)) n))
  (Q : D.PrescribedOrdinaryQuotient x (q ^ n)
    (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit (D.pointDatum x.val).data.polarized
      (D.pointDatum x.val).data.action n (s + 1) labels H) y)
  (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x.val)) (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum z)) (q ^ n))
  (hfbound : ∀ (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
    a ≫ f.isogeny.hom = 1 → a ^ (q ^ n) = 1)
  (hfchosen : ∀ (v : Fin (s + 1)) (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
    a ≫ (D.pointDatum x.val).data.action.map (j.projector iota hsplit n (labels (v, false))) = a →
      (a ≫ f.isogeny.hom = 1 ↔ ∃ h : T ⟶ (H v).group.X,
        h ≫ (H v).inclusion.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit
          (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action n
            (labels (v, false)) = a))

include Q hlabels hfbound hfchosen in
theorem point_eq_of_prescribed_chosen (hgood : D.IsGoodCompletelySplitReduction) : z = y.val := by
  let A := (D.pointDatum x.val).data.polarized
  let ρ := (D.pointDatum x.val).data.action
  let g := Intrinsic.QuotientTargets.witnessIsogeny Q.quotient
  have hg := PrescribedMapKernel.prescribed_quotient_kernel_iff D Q
  have hgbound (T : Over D.integralGeometricBase.left) (a : T ⟶ A.abelian.scheme)
      (ha : a ≫ g.isogeny.hom = 1) : a ^ (q ^ n) = 1 :=
    PrescribedKernelOf.Components.prescribed_full_kernel_killed j iota hsplit A ρ n (s + 1) labels H T a ((hg T a).mp ha)
  have hgchosen (v : Fin (s + 1)) (T : Over D.integralGeometricBase.left)
      (a : T ⟶ A.abelian.scheme)
      (ha : a ≫ ρ.map (j.projector iota hsplit n (labels (v, false))) = a) :
      a ≫ g.isogeny.hom = 1 ↔ ∃ h : T ⟶ (H v).group.X,
        h ≫ (H v).inclusion.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n
          (labels (v, false)) = a := by
    constructor
    · exact PrescribedMapKernel.prescribed_map_chosen_factor j iota hsplit A ρ n (s + 1) labels H g.isogeny.hom hg
        (Nat.le_refl n) v T a ha
    · rintro ⟨h, rfl⟩
      exact PrescribedMapKernel.prescribed_map_chosen_killed j iota hsplit A ρ n (s + 1) labels H g.isogeny.hom hg v T h
  have hfull := Geometric.PELChosenComparison.geometricPEL_full_kernel_eq_from_chosen f g j hsplit labels hlabels hfbound hgbound
    (fun v T a ha => (hfchosen v T a.val ha).trans (hgchosen v T a.val ha).symm)
  exact PointComparison.point_eq_of_prescribed_kernel f (fun T a => (hfull T a).trans (hg T a)) hgood Q

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ChosenPointComparison
