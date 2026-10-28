import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.PullbackRetraction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.RetractionIso

/-! # Retraction Carrier -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.RetractionCarrier

noncomputable section

/-! The native polarized retraction has the carrier maps of the
named canonical retraction isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S T : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (p : T ⟶ S) (r : S ⟶ T) (w : r ≫ p = 𝟙 S)

theorem polarizedRetraction_abelian :
    (PullbackRetraction.polarizedPullbackRetractionIso A p r w).abelian.hom =
      (Pullback.RetractionIso.pullbackRetractionIso p r w).hom.app A.abelian.scheme :=
  PullbackRetraction.polarizedPullbackRetractionIso_abelian A p r w

theorem polarizedRetraction_dual :
    (PullbackRetraction.polarizedPullbackRetractionIso A p r w).dual.hom =
      (Pullback.RetractionIso.pullbackRetractionIso p r w).hom.app A.dual.abelian.scheme :=
  PullbackRetraction.polarizedPullbackRetractionIso_dual A p r w

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.RetractionCarrier
