import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CohomologyTerminal

/-! # Affine Local Cohomology -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineLocalCohomology.Construction

noncomputable section

/-! Affine quasicoherent vanishing in the local-cohomology API used by Mayer-Vietoris. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.Abelian

universe u

variable (R : CommRingCat.{u})

local instance e40AffineLocalEnoughInjectives :
    EnoughInjectives (AbelianSheafInjectives.Construction.AbelianSheaves (TopCat.of (PrimeSpectrum R))) :=
  AbelianSheafInjectives.Construction.abelianSheaves_enoughInjectives (TopCat.of (PrimeSpectrum R))

local instance e40AffineLocalHasExt : HasExt.{u} (AbelianSheafInjectives.Construction.AbelianSheaves (TopCat.of (PrimeSpectrum R))) :=
  hasExt_of_enoughInjectives _

theorem quasicoherent_affine_H'_one_top_subsingleton (N : (Spec R).Modules) [N.IsQuasicoherent] :
    Subsingleton (((QuasicoherentAdditiveCech.Construction.moduleSheafToAbelian R (TopCat.of (PrimeSpectrum R))).obj
      (modulesSpecToSheaf.obj N)).H' 1 ⊤) := by
  let F : AbelianSheafInjectives.Construction.AbelianSheaves (TopCat.of (PrimeSpectrum R)) :=
    (QuasicoherentAdditiveCech.Construction.moduleSheafToAbelian R (TopCat.of (PrimeSpectrum R))).obj (modulesSpecToSheaf.obj N)
  have : Subsingleton (CategoryTheory.Sheaf.H F 1) :=
    AffineCohomologyOne.Construction.quasicoherent_affine_H_one_subsingleton R N
  exact (CohomologyTerminal.Construction.cohomologyAtTerminalIso isTerminalTop _ F 1).addCommGroupIsoToAddEquiv.injective.subsingleton

theorem quasicoherent_affine_H'_one_top_isZero (N : (Spec R).Modules) [N.IsQuasicoherent] :
    IsZero (((QuasicoherentAdditiveCech.Construction.moduleSheafToAbelian R (TopCat.of (PrimeSpectrum R))).obj
      (modulesSpecToSheaf.obj N)).H' 1 ⊤) := by
  have := quasicoherent_affine_H'_one_top_subsingleton R N
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr inferInstance

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineLocalCohomology.Construction
