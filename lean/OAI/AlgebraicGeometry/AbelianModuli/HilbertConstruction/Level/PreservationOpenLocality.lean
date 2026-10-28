import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PullbackPreservationCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationProperties
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.HomOpenCoverDetection

/-! # Preservation Open Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationOpenLocality

noncomputable section

/-! Full-level preservation can be checked after an open cover of the base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v

theorem fullLevel_preserves_of_openCover
    {S : Scheme.{u}} {g N : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}
    (l : A.FullLevel N) (k : B.FullLevel N) (f : A.scheme ⟶ B.scheme)
    (C : Scheme.OpenCover.{v} S)
    (h : ∀ i, PreservationProperties.FullLevelPreservesPullback l k f (C.f i)) :
    PreservationProperties.FullLevelPreserves l k f := by
  apply (PreservationGeometricCriterion.fullLevel_preserves_iff_geometric l k f).mpr
  apply Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks C
  intro i
  exact (PullbackPreservationCriterion.fullLevel_pullback_preserves_iff l k f (C.f i)).mpr (h i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationOpenLocality
