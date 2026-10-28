import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.PELChosenComparison

/-! # Point Isogeny Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointIsogenyComparison

noncomputable section

/-! Equal complete kernels of actual positive marked PEL isogenies
identify their original geometric target points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELTargetComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.PELChosenComparison

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  {A : D.GeometricPELDatum} {x y : D.GeometricPoint} {m : ℕ}

theorem point_eq_of_isogeny_same_kernel
    (hgood : D.IsGoodCompletelySplitReduction)
    (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily A) (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x)) m)
    (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily A) (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum y)) m)
    (h : QuotientComparison.SameKernel f.isogeny g.isogeny) : x = y := by
  let e := ActionFamilyComparison.Family.familyIsoToActionIso (PELTargetComparison.quotientPELIso f g h)
  have hx := D.pointOfPEL_eq_of_pointDatumIso hgood x (D.pointDatum x)
    (PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.refl _)
  have hy := D.pointOfPEL_eq_of_pointDatumIso hgood y (D.pointDatum y)
    (PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.refl _)
  exact hx.symm.trans ((Intrinsic.QuotientTargets.pointOfPEL_eq_of_iso hgood _ _ e).trans hy)

theorem point_eq_of_isogeny_chosen
    (hgood : D.IsGoodCompletelySplitReduction)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
    (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
    (hlabels : ∀ v : Fin s, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
    (n : ℕ)
    (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily A) (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x)) (q ^ n))
    (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily A) (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum y)) (q ^ n))
    (hf : ∀ (T : Over D.integralGeometricBase.left) (a : T ⟶ A.data.polarized.abelian.scheme),
      a ≫ f.isogeny.hom = 1 → a ^ (q ^ n) = 1)
    (hg : ∀ (T : Over D.integralGeometricBase.left) (a : T ⟶ A.data.polarized.abelian.scheme),
      a ≫ g.isogeny.hom = 1 → a ^ (q ^ n) = 1)
    (hc : ∀ (v : Fin s) (T : Over D.integralGeometricBase.left)
      (a : (A.data.polarized.abelian.torsionFunctor (q ^ n)).obj (.op T)),
      a.val ≫ A.data.action.map (j.projector iota hsplit n (labels (v, false))) = a.val →
        (a.val ≫ f.isogeny.hom = 1 ↔ a.val ≫ g.isogeny.hom = 1)) : x = y :=
  point_eq_of_isogeny_same_kernel hgood f g
    (Geometric.PELChosenComparison.geometricPEL_full_kernel_eq_from_chosen f g j hsplit labels hlabels hf hg hc)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointIsogenyComparison
