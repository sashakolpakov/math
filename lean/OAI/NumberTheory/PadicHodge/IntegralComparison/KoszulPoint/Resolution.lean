import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DuplicateFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionOrientation

/-! # Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Resolution.Comparison

noncomputable section

/-! The product point Koszul complex and the standard concatenated
Koszul complex have the same literal quotient augmentation. Their
comparisons from any fixed original resolution therefore agree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
variable (R : Type u) [CommRing R] {c m : ℕ}
  (s : Fin c → R) (t : Fin m → R)
  (hst : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.append s t)))

theorem full_ideal : Koszul.OrientedTopCohomology.ideal R (Fin.append s t) =
    KoszulPartial.Resolution.pointIdeal R s t := by
  change Koszul.OrientedTopCohomology.ideal R (Fin.append s t) =
    Koszul.OrientedTopCohomology.ideal R
      (fun i => KoszulPartial.Differential.equation R s t (KoszulPartial.TopResidue.basis R i))
  rw [KoszulPartial.Resolution.basis_values]

abbrev fullResolution : ProjectiveResolution (ModuleCat.of R (R ⧸ KoszulPartial.Resolution.pointIdeal R s t)) :=
  Koszul.ResolutionOrientation.resolutionAtIdeal R (KoszulPartial.Resolution.pointIdeal R s t)
    (Fin.append s t) (full_ideal R s t) hst

theorem augmentation : (Koszul.DuplicateFraction.pointIso R s t).hom ≫
    (KoszulPartial.Resolution.pointResolution R s t hst).π = (fullResolution R s t hst).π := by
  apply HomologicalComplex.Hom.ext
  funext q
  cases q with
  | zero =>
      rw [HomologicalComplex.comp_f]
      change (Koszul.DuplicateFraction.pointIso R s t).hom.f 0 ≫
          (Exterior.KoszulBasisResolution.resolution R (KoszulPartial.TopResidue.basis R)
            (KoszulPartial.Differential.equation R s t) _).π.f 0 =
        (Koszul.ResolutionOrientation.resolutionAtIdeal R (KoszulPartial.Resolution.pointIdeal R s t)
          (Fin.append s t) (full_ideal R s t) hst).π.f 0
      rw [Exterior.KoszulBasisResolution.resolution_π_zero,
        Koszul.ResolutionOrientation.resolutionAtIdeal_π_zero]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (KoszulPartial.Resolution.pointIdeal R s t).mkQ
          (exteriorPower.zeroEquiv R (KoszulPartial.Fractions.ambient R (c := c) (m := m))
            (exteriorPower.map 0 (KoszulPartial.TopResidue.basis R).equivFun.symm.toLinearMap x)) =
        (KoszulPartial.Resolution.pointIdeal R s t).mkQ (exteriorPower.zeroEquiv R (Fin (c+m) → R) x)
      exact congrArg (KoszulPartial.Resolution.pointIdeal R s t).mkQ (LinearMap.congr_fun
        (exteriorPower.zeroEquiv_naturality
          (KoszulPartial.TopResidue.basis R).equivFun.symm.toLinearMap) x)
  | succ q =>
      exact (isZero_single_obj_X (.down ℕ) 0
        (ModuleCat.of R (R ⧸ KoszulPartial.Resolution.pointIdeal R s t)) (q+1) (by omega)).eq_of_tgt _ _

theorem comparison
    (Q : ProjectiveResolution (ModuleCat.of R (R ⧸ KoszulPartial.Resolution.pointIdeal R s t))) (q : ℕ) :
    (IntegralComparison.ProjectiveResolution.Hom.Comparison.homologyIso (ExactModuleDualFunctor.functor R)
      Q (KoszulPartial.Resolution.pointResolution R s t hst) q).hom ≫
        homologyMap (DualComplexHomology.map R (Koszul.DuplicateFraction.pointIso R s t).hom) q =
    (IntegralComparison.ProjectiveResolution.Hom.Comparison.homologyIso (ExactModuleDualFunctor.functor R)
      Q (fullResolution R s t hst) q).hom :=
  Koszul.ResolutionOrientation.comparison_naturality R Q (KoszulPartial.Resolution.pointResolution R s t hst)
    (fullResolution R s t hst) (Koszul.DuplicateFraction.pointIso R s t).hom
    (augmentation R s t hst) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Resolution.Comparison
