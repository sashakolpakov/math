import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualBaseChangeComparison

/-! # Pulled Polarization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PulledPolarization.Construction

noncomputable section

/-! The pulled polarization preserves the canonical group of the
literal pulled Picard datum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false in
theorem noetherian_pulled_polarization_isMonHom
    {S S' : Scheme.{0}} [IsLocallyNoetherian S'] {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (s : S' ⟶ S) :
    IsMonHom (show (A.pullback s).scheme ⟶ ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).pullback s).withPicardGroup.abelian
      from (pol.pullback s).isogeny.hom) := by
  have h := PolarizationAdapter.Construction.originalPolarization_preserves_canonical_group_over_noetherian_base
    (A.pullback s) (D.pullback s) (pol.pullback s)
  simpa only [FrobeniusKernel.DualBaseChangeComparison.Construction.nativeDualData_ofBundled_pullback] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PulledPolarization.Construction
