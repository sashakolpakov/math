import OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticIsolatedDimension
import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothBaseNeighborhood

/-! # Intrinsic Isolated Point -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicIsolatedPoint.Abelian

noncomputable section

/-!
Analytic isolation of an actual complex point in a smooth scheme implies
scheme-theoretic isolation. The proof constructs a standard-smooth affine
neighborhood and proves its zero dimension, rather than assuming that the
native and Zariski topologies have the same open sets.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem scheme_isolated_of_native_isolated
    (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth S.hom] (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hs : IsOpen ({s} : Set (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S))) :
    IsOpen {s.left (IsLocalRing.closedPoint ℂ)} := by
  obtain ⟨R, b, hb, y, P, hy⟩ := SmoothBaseNeighborhood.Abelian.RelativeCharts.exists_smooth_affine_base_neighborhood S s
  let : IsOpenImmersion b.left := hb
  let e := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap R b
  have he := AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap R b
  have hpre : e ⁻¹' {s} = {y} := by
    ext z
    change e z = s ↔ z = y
    rw [← hy]
    exact he.injective.eq_iff
  have hyopen : IsOpen ({y} : Set (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R)) := by
    rw [← hpre]
    exact hs.preimage he.continuous
  let : IsArtinianRing R := AnalyticIsolatedDimension.Abelian.standardSmooth_artinian_of_analytic_isolated P.presentation y hyopen
  let : DiscreteTopology (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).left :=
    inferInstanceAs (DiscreteTopology (PrimeSpectrum R))
  let z : (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).left := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (A := R) y
  have hkernel : IsOpen ({z} : Set (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).left) := isOpen_discrete _
  have himage : IsOpen (b.left '' ({z} : Set (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).left)) := b.left.isOpenMap _ hkernel
  have hpoint : b.left z =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying s :=
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying_affinePointMap R b y).symm.trans
      (congrArg AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying hy)
  have hscheme : IsOpen {AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying s} := by
    rw [Set.image_singleton] at himage
    exact (congrArg (fun w : S.left => IsOpen ({w} : Set S.left)) hpoint).mp himage
  have hbase : IsLocalRing.closedPoint ℂ = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint := Subsingleton.elim _ _
  rw [hbase]
  exact hscheme

end

end OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicIsolatedPoint.Abelian
