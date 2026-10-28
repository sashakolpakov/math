import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointwiseGeneratingPower
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.GeometricAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerStability

/-! # Pointwise Geometric Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! For a proper scheme over an affine base, geometric fiber ampleness and pointwise nonvanishing sections of positive powers imply ampleness and projectivity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S X : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsProper f] (L : Line.Bundles.LineBundle X)
variable (hL : ∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ S),
  (L.pullback (Limits.pullback.fst f b)).IsAmple)
variable (h : ∀ x : X, ∃ (n : ℕ) (_ : 0 < n) (s : Line.Bundles.structureModule X ⟶ (L.tensorPower n).sheaf),
  x ∈ Ample.LineBundles.sectionNonvanishing s)

include hL h

theorem Line.Bundles.LineBundle.isAmple_of_geometric_fibers_of_pointwise_sections : L.IsAmple := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨d, hd, n, s, hs⟩ := L.exists_generating_power_of_pointwise h
  have ha : (L.tensorPower d).IsAmple := by
    apply (L.tensorPower d).isAmple_of_geometric_fibers_of_generating_sections f s hs
    intro K _ _ b
    exact ((hL K b).tensorPower d hd).of_iso (L.powerBaseChangeIso (Limits.pullback.fst f b) d).symm
  exact ha.of_tensorPower d hd

def Line.Bundles.LineBundle.projectivePresentation_of_geometric_fibers_of_pointwise_sections : Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f) :=
  (L.isAmple_of_geometric_fibers_of_pointwise_sections f hL h).projectivePresentation f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
