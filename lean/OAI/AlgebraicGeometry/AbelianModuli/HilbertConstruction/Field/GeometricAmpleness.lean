import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExtensionPowerSectionDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointwiseGeometricProjectivity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Geometric Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! For a proper scheme over a field, a line bundle ample after every geometric field extension is already ample and gives a projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of K)) [IsProper p] (L : Line.Bundles.LineBundle X)
variable (hL : ∀ (F : Type u) [Field F] [IsAlgClosed F] (b : Spec (.of F) ⟶ Spec (.of K)),
  (L.pullback (Limits.pullback.fst p b)).IsAmple)

include hL

theorem Line.Bundles.LineBundle.isAmple_of_geometric_fibers_overField : L.IsAmple := by
  let φ : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) :=
    CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))
  exact L.isAmple_of_geometric_fibers_of_pointwise_sections p hL
    (L.pointwise_power_sections_of_ample_fieldExtension p φ (hL (AlgebraicClosure K) (Spec.map φ)))

def Line.Bundles.LineBundle.projectivePresentation_of_geometric_fibers_overField : Projective.ProjectivePresentations.ProjectivePresentation (Over.mk p) :=
  (L.isAmple_of_geometric_fibers_overField p hL).projectivePresentation p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
