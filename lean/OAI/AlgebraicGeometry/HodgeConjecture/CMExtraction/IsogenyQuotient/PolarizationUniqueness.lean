import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PolarizationCancellation
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELPicardDualMaps

/-! # Polarization Uniqueness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.PolarizationUniqueness

noncomputable section

/-! TateComparison's uniqueness among all group maps follows on the retained
Noetherian cover from native polarization cancellation. It is not added
as a stronger premise to the full IsogenyQuotient positive-polarization statement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELPicardDualMaps

variable {R : Type} [CommRing R] {S : Scheme} [IsLocallyNoetherian S]
  {g N n : ℕ} {A B : AbelianScheme.TateComparison.PEL.PELFamilyData R g N S}

theorem polarization_unique_group_map (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B n)
    (p : B.abelian.scheme ⟶ B.dual.abelian.scheme) [IsMonHom p]
    (hp : f.isogeny.hom ≫ p ≫ f.dualHom = A.polarizationMap.hom ^ n) :
    p = B.polarizationMap.hom := by
  apply AbelianScheme.IsogenyQuotient.Noetherian.PolarizationCancellation.Construction.noetherian_polarizationPullback_injective f.isogeny A.dual B.dual
  have hd : f.dualHom = AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.isogeny.hom A.dual B.dual :=
    AbelianScheme.FrobeniusKernel.PicardAdjoints.Construction.NativePicardPullback.dualMap_eq_of_poincare f.isogeny.hom A.dual B.dual
      f.dualHom f.poincare.symm
  rw [← hd]
  exact hp.trans f.polarization.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.PolarizationUniqueness
