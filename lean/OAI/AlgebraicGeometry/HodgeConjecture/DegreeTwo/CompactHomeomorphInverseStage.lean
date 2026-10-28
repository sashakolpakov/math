import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph

/-! # Compact Homeomorph Inverse Stage -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactHomeomorphInverseStage.Constructions

noncomputable section

/-! Inverse homeomorphism transport on each actual compact cohomology stage. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph

theorem compactHomeomorph_inverse_stage {X Y : TopCat.{0}} (e : X ≃ₜ Y) (K : Compacts X) (n : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K n ≫
      (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ) e n).inv =
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportHomeomorphStageCohomologyIso (ModuleCat.of ℚ ℚ) e K n).inv ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) Y (Compacts.equiv e K) n := by
  apply (cancel_epi (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportHomeomorphStageCohomologyIso (ModuleCat.of ℚ ℚ) e K n).hom).mp
  rw [← Category.assoc, ← AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso_ι, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactHomeomorphInverseStage.Constructions
