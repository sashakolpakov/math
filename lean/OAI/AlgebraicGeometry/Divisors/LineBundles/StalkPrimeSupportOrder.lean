import OAI.AlgebraicGeometry.Divisors.LineBundles.StalkPrimeSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.StalkRationalOrder

/-! # Stalk Prime Support Order -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.StalkPrimeSupportOrder.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual local rings and orders on the localized prime support
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme) [AlgebraicGeometry.IsNoetherian X] (x : X) (p : Spec (X.presheaf.stalk x))

theorem pointSupportMap_fromSpecStalk_stalkMap_isIso
    (q : CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm p)) :
    IsIso ((Point.SupportMap.BundleCycles.pointSupportMap (X.fromSpecStalk x) p).stalkMap q) := by
  let W := StalkPrimeSupport.BundleCycles.stalkPrimeGlobalSupport X x p
  let y := StalkSupportKernel.BundleCycles.supportLocalPoint X W x (StalkPrimeSupport.BundleCycles.stalkPrimeGlobalSupport_mem X x p)
  let e := StalkPrimeSupport.BundleCycles.stalkPrimeSupportIso X x p
  rw [StalkPrimeSupport.BundleCycles.pointSupportMap_fromSpecStalk_factorization, Scheme.Hom.stalkMap_comp]
  have hi : IsIso (e.inv.stalkMap q) := inferInstance
  have hj := StalkLocalization.BundleCycles.fromSpecStalk_stalkMap_isIso (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) y (e.inv q)
  exact ((@asIso _ _ _ _ _ hj) ≪≫ (@asIso _ _ _ _ _ hi)).isIso_hom

theorem pointSupportMap_fromSpecStalk_coheight
    (q : CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm p)) :
    coheight (Point.SupportMap.BundleCycles.pointSupportMap (X.fromSpecStalk x) p q) = coheight q := by
  rw [StalkPrimeSupport.BundleCycles.pointSupportMap_fromSpecStalk_factorization, Scheme.Hom.comp_apply, StalkLocalization.BundleCycles.fromSpecStalk_coheight]
  exact coheight_eq_of_isOpenImmersion (StalkPrimeSupport.BundleCycles.stalkPrimeSupportIso X x p).inv

theorem pointSupportFunctionFieldMap_fromSpecStalk_isIso :
    IsIso (Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap (X.fromSpecStalk x) p) := by
  let A := CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm p)
  let B := CycleClass.Geometric.GenericPoint.reducedSupportScheme (StalkPrimeSupport.BundleCycles.stalkPrimeGlobalSupport X x p)
  let r := Point.SupportMap.BundleCycles.pointSupportMap (X.fromSpecStalk x) p
  let hη := Point.SupportNaturality.BundleCycles.pointSupportMap_genericPoint (X.fromSpecStalk x) p r (Point.SupportMap.BundleCycles.pointSupportMap_inclusion (X.fromSpecStalk x) p)
  let e := B.presheaf.stalkCongr (Inseparable.of_eq hη.symm)
  exact (e ≪≫ (@asIso _ _ _ _ _ (pointSupportMap_fromSpecStalk_stalkMap_isIso X x p (genericPoint A)))).isIso_hom

omit [AlgebraicGeometry.IsNoetherian X] in
theorem pointSupport_fromSpecStalk_preimage :
    X.fromSpecStalk x ⁻¹' (StalkPrimeSupport.BundleCycles.stalkPrimeGlobalSupport X x p : Set X) =
      (irreducibleSetEquivPoints.symm p : Set (Spec (X.presheaf.stalk x))) := by
  ext q
  change X.fromSpecStalk x q ∈ closure {X.fromSpecStalk x p} ↔ q ∈ closure {p}
  rw [← specializes_iff_mem_closure, ← specializes_iff_mem_closure]
  exact (X.fromSpecStalk x).isEmbedding.isInducing.specializes_iff

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.StalkPrimeSupportOrder.BundleCycles
