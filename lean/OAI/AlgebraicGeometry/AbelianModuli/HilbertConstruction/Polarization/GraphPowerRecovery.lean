import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.PolarizationGraphPowerRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosureFieldPullbackEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.PolarizedDualHomDetection

/-! # Graph Power Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A positive tensor power of the canonical graph bundle determines
the polarization map on a fixed dual over every locally Noetherian base,
including bases with nilpotents. Geometric positivity supplies all
symmetry conditions used in the recovery argument. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i)

include hδ

theorem PolarizationData.PolarizedAbelianWithFullLevel.polarization_hom_eq_of_graphPower (p : PolarizationData.Polarization A.dual δ) (d : ℕ) (hd : 0 < d)
    (he : Line.Bundles.LineBundle.classOf A.graphBundle ^ d =
      Line.Bundles.LineBundle.classOf (PoincareGraph.Bundles.poincareGraphBundle A.dual p.isogeny.hom) ^ d) :
    A.polarization.isogeny.hom = p.isogeny.hom := by
  apply A.dualHom_eq_of_fieldPullbacks hδ
  exact ClosureFieldPullbackEquality.overHom_fieldPullbacks_eq_of_algClosed A.polarization.isogeny.hom p.isogeny.hom
    (A.polarization_graphPower_geometric_recovery hδ p d hd he)

theorem PolarizationData.PolarizedAbelianWithFullLevel.polarization_hom_eq_of_graphPower_bundleIso (p : PolarizationData.Polarization A.dual δ)
    (d : ℕ) (hd : 0 < d)
    (e : (A.graphBundle.tensorPower d).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle A.dual p.isogeny.hom).tensorPower d).sheaf) :
    A.polarization.isogeny.hom = p.isogeny.hom := by
  apply A.polarization_hom_eq_of_graphPower hδ p d hd
  have he : Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower d) =
      Line.Bundles.LineBundle.classOf ((PoincareGraph.Bundles.poincareGraphBundle A.dual p.isogeny.hom).tensorPower d) := Quotient.sound ⟨e⟩
  simpa only [Line.Bundles.LineBundle.classOf_tensorPower] using he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
