import OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiHomeomorphism
import OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianSheafUniverses
import OAI.AlgebraicGeometry.SheafCohomology.AffineVanishing
import OAI.AlgebraicGeometry.SheafCohomology.ExtNaturality

/-! # Affine Acyclicity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.AffineAcyclicity

noncomputable section

/-!
# IntegralComparison: affine structure-sheaf acyclicity in the crystalline value universe

The spectrum of the lifted ambient ring is homeomorphic to the original
spectrum. Native affine acyclicity on the lifted spectrum and the proved
Zariski cohomology transport give vanishing with the larger abelian-group
values used by the original crystalline site.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable (R : Type u) [CommRing R]

abbrev LiftedRing := ULift.{u + 1} R

def spectrumHomeomorph : PrimeSpectrum (LiftedRing R) ≃ₜ PrimeSpectrum R :=
  PrimeSpectrum.homeomorphOfRingEquiv ULift.ringEquiv

def affineUnit : (Spec (CommRingCat.of (LiftedRing R))).Modules :=
  tilde (ModuleCat.of (CommRingCat.of (LiftedRing R)) (LiftedRing R))

instance affineUnit_quasicoherent : (affineUnit R).IsQuasicoherent := by
  unfold affineUnit
  infer_instance

abbrev NativeSheaf := Sheaf (Opens.grothendieckTopology (PrimeSpectrum (LiftedRing R))) AddCommGrpCat.{u + 1}
abbrev AmbientSheaf := Sheaf (Opens.grothendieckTopology (PrimeSpectrum R)) AddCommGrpCat.{u + 1}

instance ambientHasSheafify :
    HasSheafify (Opens.grothendieckTopology (PrimeSpectrum R)) AddCommGrpCat.{u + 1} :=
  AbelianSheafUniverses.hasSheafify.{u + 1, u, u} _

instance nativeEnoughInjectives : EnoughInjectives (NativeSheaf R) :=
  AbelianSheafUniverses.enoughInjectives.{u + 1, u + 1, u + 1} _

instance ambientEnoughInjectives : EnoughInjectives (AmbientSheaf R) :=
  AbelianSheafUniverses.enoughInjectives.{u + 1, u, u} _

instance nativeHasExt : HasExt.{u + 2} (NativeSheaf R) := HasExt.standard _
instance nativeSmallHasExt : HasExt.{u + 1} (NativeSheaf R) := hasExt_of_enoughInjectives _
instance ambientHasExt : HasExt.{u + 2} (AmbientSheaf R) := HasExt.standard _

def nativeUnitSheaf : NativeSheaf R :=
  (SheafOfModules.toSheaf (Spec (CommRingCat.of (LiftedRing R))).ringCatSheaf).obj (affineUnit R)

def unitSheaf : AmbientSheaf R :=
  (ZariskiHomeomorphism.sheafEquiv (spectrumHomeomorph R) AddCommGrpCat.{u + 1}).functor.obj
    (nativeUnitSheaf R)

abbrev constantUnit : AmbientSheaf R :=
  (constantSheaf (Opens.grothendieckTopology (PrimeSpectrum R)) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

def cohomologyEquiv (n : ℕ) : AlgebraicGeometry.SheafCohomology.AffineH.Projective.H (affineUnit R) n ≃+
    Abelian.Ext.{u + 2} (constantUnit R) (unitSheaf R) n :=
  (AlgebraicGeometry.SheafCohomology.ExtNaturality.Projective.extChangeUniverseAddEquiv.{u + 2, u + 1, u + 1, u + 2}
    ((constantSheaf (Opens.grothendieckTopology (PrimeSpectrum (LiftedRing R))) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) (nativeUnitSheaf R) n).trans
    (ZariskiHomeomorphism.cohomologyEquiv.{u + 1, u, u + 2, u + 1, u + 2}
      (spectrumHomeomorph R) AddCommGrpCat.{u + 1}
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (nativeUnitSheaf R) n)

theorem positive_cohomology_zero (q : ℕ) :
    Subsingleton (Abelian.Ext.{u + 2} (constantUnit R) (unitSheaf R) (q + 1)) := by
  let := AlgebraicGeometry.SheafCohomology.AffineVanishing.Projective.moduleSpecHSucc_subsingleton (affineUnit R) q
  exact (cohomologyEquiv R (q + 1)).symm.toEquiv.subsingleton

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.AffineAcyclicity
