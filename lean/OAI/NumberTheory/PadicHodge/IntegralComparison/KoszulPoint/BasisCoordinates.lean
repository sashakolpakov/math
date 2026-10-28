import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DuplicateFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DeterminantTransition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TopCycleClass

/-! # Basis Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.BasisCoordinates

noncomputable section

/-! The standard point Koszul coordinates and the ordered normal/parameter
coordinates have precisely the same top coefficient. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorCoordinates
variable (R : Type u) [CommRing R] {c m : ℕ} (s : Fin c → R) (t : Fin m → R)

 theorem inverse_generator :
    (Koszul.DuplicateFraction.pointIso R s t).inv.f (c+m)
      (TopExteriorCoordinates.generator (KoszulPartial.TopResidue.basis R (c := c) (m := m))) =
        TopExteriorCoordinates.generator (Pi.basisFun R (Fin (c+m))) := by
  change exteriorPower.map (c+m) (KoszulPartial.TopResidue.basis R).equivFun.toLinearMap
    (exteriorPower.ιMulti R (c+m) (KoszulPartial.TopResidue.basis R)) = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i j
  simp only [Function.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_self,
    Pi.basisFun_apply, Pi.single_apply, eq_comm]

 def functional (ψ : Module.Dual R (⋀[R]^(c+m) (Fin (c+m) → R))) :
    Module.Dual R (⋀[R]^(c+m) (KoszulPartial.Fractions.ambient R (c := c) (m := m))) :=
  (DualComplexHomology.map R (Koszul.DuplicateFraction.pointIso R s t).inv).f (c+m) ψ

 theorem evaluation (ψ : Module.Dual R (⋀[R]^(c+m) (Fin (c+m) → R))) :
    functional R s t ψ (TopExteriorCoordinates.generator (KoszulPartial.TopResidue.basis R)) =
      Koszul.OrientedTopCohomology.evaluation R (Fin.append s t) ψ := by
  change ψ ((Koszul.DuplicateFraction.pointIso R s t).inv.f (c+m)
    (TopExteriorCoordinates.generator (KoszulPartial.TopResidue.basis R))) = _
  rw [inverse_generator]
  rfl

 theorem outgoing_isZero : IsZero ((KoszulPartial.Components.source R s t).X ((ComplexShape.up ℕ).next (c+m))) := by
  have hz := Exterior.PowerVanishing.subsingleton
    (KoszulPartial.TopResidue.basis R (c := c) (m := m)) (Nat.lt_succ_self (c+m))
  let : Subsingleton ((KoszulPartial.Components.source R s t).X ((ComplexShape.up ℕ).next (c+m))) := by
    rw [CochainComplex.next]
    change Subsingleton (Module.Dual R (⋀[R]^(c+m+1) (KoszulPartial.Fractions.ambient R (c := c) (m := m))))
    let := hz
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

 theorem class_coordinates (ψ : Module.Dual R (⋀[R]^(c+m) (Fin (c+m) → R))) :
    homologyMap (DualComplexHomology.map R (Koszul.DuplicateFraction.pointIso R s t).hom) (c+m)
      (KoszulPartial.PartialClass.sourceClass R s t (functional R s t ψ)) =
        TopHomologyCokernel.cycleClass
          (Koszul.OrientedTopCohomology.dualComplex R (Fin.append s t)) (c+m)
          (Koszul.OrientedTopCohomology.outgoing_isZero R (Fin.append s t)) ψ := by
  rw [KoszulPartial.PartialClass.sourceClass,
    IntegralComparison.Module.TopCycleClass.apply (KoszulPartial.Components.source R s t) (c+m) (outgoing_isZero R s t)]
  have h := ConcreteCategory.congr_hom
    (Koszul.DeterminantTransition.cycleClass_naturality
      (DualComplexHomology.map R (Koszul.DuplicateFraction.pointIso R s t).hom) (c+m)
      (outgoing_isZero R s t) (Koszul.OrientedTopCohomology.outgoing_isZero R (Fin.append s t)))
    (functional R s t ψ)
  change _ = TopHomologyCokernel.cycleClass
    (Koszul.OrientedTopCohomology.dualComplex R (Fin.append s t)) (c+m)
    (Koszul.OrientedTopCohomology.outgoing_isZero R (Fin.append s t))
    ((DualComplexHomology.map R (Koszul.DuplicateFraction.pointIso R s t).hom).f (c+m)
      (functional R s t ψ)) at h
  refine h.trans ?_
  congr 1
  apply LinearMap.ext
  intro x
  change ψ ((Koszul.DuplicateFraction.pointIso R s t).inv.f (c+m)
    ((Koszul.DuplicateFraction.pointIso R s t).hom.f (c+m) x)) = ψ x
  exact congrArg ψ (ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (Koszul.DuplicateFraction.pointIso R s t).hom_inv_id (c+m)) x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.BasisCoordinates
