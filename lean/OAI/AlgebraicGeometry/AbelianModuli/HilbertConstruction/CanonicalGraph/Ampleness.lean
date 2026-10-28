import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphFiberAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles

/-! # Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Canonical graph-bundle ampleness for polarized objects and their geometric fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_ample_geometricFiber
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (K : Type u) [Field K] [IsAlgClosed K]
    (f : Spec (.of K) ⟶ S) :
    (A.graphBundle.pullback (Limits.pullback.fst A.abelian.scheme.hom f)).IsAmple :=
  A.polarization.graphBundle_ample_geometricFiber K f

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_isAmple_overAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) :
    A.graphBundle.IsAmple :=
  (Line.Bundles.LineBundle.isAmple_pullback_iff_of_isIso (Limits.pullback.fst A.abelian.scheme.hom (𝟙 _))).mp
    (A.graphBundle_ample_geometricFiber K (𝟙 _))

theorem PolarizationData.PolarizedAbelianWithFullLevel.pulledBackGraphBundle_isAmple
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (K : Type u) [Field K] [IsAlgClosed K]
    (f : Spec (.of K) ⟶ S) : (A.pullback f).graphBundle.IsAmple :=
  (A.graphBundle_ample_geometricFiber K f).of_iso (A.graphBundle_baseChangeIso f).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
