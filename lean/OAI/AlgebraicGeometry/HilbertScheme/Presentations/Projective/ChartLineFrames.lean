import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.LineBundleFrames
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartPolynomialEquiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Chart Line Frames -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartLineFrames

noncomputable section

/-! Every line bundle on projective space over a field is trivial on
each standard affine chart, with an actual isomorphism of module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ} (i : Fin (n + 1))

instance projectiveChartRing_isDomain : IsDomain (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing K n i) :=
  (ChartPolynomialEquiv.projectiveChartPolynomialEquiv K i).toRingEquiv.toMulEquiv.isDomain _

instance projectiveChartRing_uniqueFactorization : UniqueFactorizationMonoid (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing K n i) :=
  (ChartPolynomialEquiv.projectiveChartPolynomialEquiv K i).symm.toRingEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance

def projectiveChartLineFrame (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n))) :
    (Scheme.Modules.pullback (Proj.awayι (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)
      (isHomogeneous_X K i) Nat.zero_lt_one)).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing K n i))) :=
  Affine.LineBundleFrames.affineLineBundleFrame (L.pullback (Proj.awayι (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)
    (isHomogeneous_X K i) Nat.zero_lt_one))

def projectiveOpenLineFrame (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n))) :
    (Scheme.Modules.pullback (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)).ι).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)).toScheme := by
  let e := Proj.basicOpenIsoSpec (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)
    (isHomogeneous_X K i) Nat.zero_lt_one
  have h : e.hom ≫ Proj.awayι (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)
      (isHomogeneous_X K i) Nat.zero_lt_one = (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)).ι := by
    change e.hom ≫ (e.inv ≫ _) = _
    exact e.hom_inv_id_assoc _
  exact (Scheme.Modules.pullbackCongr h.symm).app L.sheaf ≪≫
    ((Scheme.Modules.pullbackComp e.hom (Proj.awayι (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)
      (isHomogeneous_X K i) Nat.zero_lt_one)).app L.sheaf).symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso (projectiveChartLineFrame K i L) ≪≫
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso e.hom

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartLineFrames
