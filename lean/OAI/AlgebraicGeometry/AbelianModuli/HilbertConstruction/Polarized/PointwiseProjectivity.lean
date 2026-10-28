import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointwiseGeometricProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.Ampleness

/-! # Pointwise Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On an affine base, the canonical polarization bundle is ample exactly when its positive powers have pointwise nonvanishing global sections. Those sections give an actual projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} [IsAffine S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_isAmple_iff_pointwise_power_sections :
    A.graphBundle.IsAmple ↔
      ∀ x : A.abelian.scheme.left, ∃ (n : ℕ) (_ : 0 < n)
        (s : Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower n).sheaf),
        x ∈ Ample.LineBundles.sectionNonvanishing s := by
  constructor
  · intro h x
    obtain ⟨n, hn, s, hx, _⟩ := (A.graphBundle.isAmple_iff_tensorPower.mp h).2 x
    exact ⟨n, hn, s, hx⟩
  · intro h
    exact A.graphBundle.isAmple_of_geometric_fibers_of_pointwise_sections A.abelian.scheme.hom
      (A.graphBundle_ample_geometricFiber) h

def PolarizationData.PolarizedAbelianWithFullLevel.projectivePresentation_of_pointwise_graph_sections
    (h : ∀ x : A.abelian.scheme.left, ∃ (n : ℕ) (_ : 0 < n)
      (s : Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower n).sheaf),
      x ∈ Ample.LineBundles.sectionNonvanishing s) : Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme :=
  ((A.graphBundle_isAmple_iff_pointwise_power_sections).mpr h).projectivePresentation A.abelian.scheme.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
