import OAI.AlgebraicGeometry.SheafCohomology.AffineLocalKilling
import OAI.AlgebraicGeometry.SheafCohomology.DimensionShift

/-! # Affine One -/

namespace OAI.AlgebraicGeometry.SheafCohomology.AffineOne.Projective

noncomputable section

/-!
# Degree-one affine quasicoherent acyclicity

This file proves that genuine Ext-based degree-one Zariski cohomology of a
quasicoherent scheme module on an affine spectrum vanishes. Given a class,
`schemeHOne_finiteAffineKillingCover` constructs a finite affine cover whose
actual cover-module map kills it. Quasicoherence makes the cokernel
projection surjective on genuine `H⁰`, so the long exact sequence makes that
cover-module map injective on genuine `H¹`. The class is therefore zero.

This is the first positive-degree affine-vanishing theorem in the project.
Higher degrees still require iterating local killing and dimension shifting;
no higher-degree claim is made here.
-/

universe u

open _root_.CategoryTheory Limits _root_.TopologicalSpace
open _root_.AlgebraicGeometry

/-- For a finite affine open cover of an affine spectrum, the actual map into
the product of restriction-pushforwards is injective on genuine `H¹` of a
quasicoherent scheme module. -/
theorem toAffineCoverModule_HOne_injective
    {R : CommRingCat.{u}} {I : Type u} [Finite I]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (U : I → (Spec R).Opens) (hU : IsOpenCover U)
    [∀ i, IsAffine (U i)] :
    Function.Injective
      ((AffineH.Projective.zariskiFunctor (Spec R) 1).map
        (AffineCover.Projective.toAffineCoverModule M U)) := by
  let : (AffineCover.Projective.affineCoverModule M U).IsQuasicoherent :=
    AffineCover.Projective.affineCoverModule_isQuasicoherent M U
  have hsurjective : Function.Surjective
      ((AffineH.Projective.zariskiFunctor (Spec R) 0).map
        (cokernel.π (AffineCover.Projective.toAffineCoverModule M U))) :=
    AffineExact.Projective.moduleSpecHZero_surjective_cokernel_pi
      (AffineCover.Projective.toAffineCoverModule M U)
  exact DimensionShift.ProjectiveAffine.cohomology_succ_map_injective_of_previous_surjective
    (AffineCoverMono.Projective.affineCoverCokernel_shortExact M U hU) 0 hsurjective

/-- Genuine Ext-based `H¹` of a quasicoherent scheme module on an affine
spectrum is subsingleton. -/
theorem moduleSpecHOne_subsingleton
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] : Subsingleton (AffineH.Projective.H M 1) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨I, U, hfinite, hcover, haffine, _, hkilled⟩ :=
    AffineLocalKilling.Projective.LocalKilling.schemeHOne_finiteAffineKillingCover M c
  let : Finite I := hfinite
  let (i : I) : IsAffine (U i) := haffine i
  apply toAffineCoverModule_HOne_injective M U hcover
  rw [hkilled, map_zero]

/-- Every genuine Ext-based degree-one class of a quasicoherent scheme
module on an affine spectrum is zero. -/
theorem moduleSpecHOne_eq_zero
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] (c : AffineH.Projective.H M 1) : c = 0 := by
  let : Subsingleton (AffineH.Projective.H M 1) := moduleSpecHOne_subsingleton M
  exact Subsingleton.elim _ _

end

end OAI.AlgebraicGeometry.SheafCohomology.AffineOne.Projective
