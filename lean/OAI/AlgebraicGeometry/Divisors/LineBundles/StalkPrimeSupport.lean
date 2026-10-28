import OAI.AlgebraicGeometry.Divisors.LineBundles.StalkSupportKernel
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage

/-! # Stalk Prime Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.StalkPrimeSupport.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: the actual local prime support is the spectrum of the support stalk

The surjective support stalk map gives a closed immersion. Its kernel
identification computes its reduced image exactly, yielding an actual
scheme isomorphism with the corresponding prime closure in Spec O_X,x.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme) (W : IrreducibleCloseds X) (x : X) (hx : x ∈ (W : Set X))

def supportLocalSpectrumMap :
    Spec ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (StalkSupportKernel.BundleCycles.supportLocalPoint X W x hx)) ⟶
      Spec (X.presheaf.stalk x) := Spec.map (StalkSupportKernel.BundleCycles.supportLocalStalkMap X W x hx)

instance supportLocalSpectrumMap_isClosedImmersion : IsClosedImmersion (supportLocalSpectrumMap X W x hx) :=
  IsClosedImmersion.spec_of_surjective (StalkSupportKernel.BundleCycles.supportLocalStalkMap X W x hx)
    (StalkSupportKernel.BundleCycles.supportLocalStalkMap_surjective X W x hx)

theorem supportLocalSpectrumMap_genericPoint :
    supportLocalSpectrumMap X W x hx (genericPoint _) = StalkSupportKernel.BundleCycles.supportLocalKernelPrime X W x hx := by
  rw [genericPoint_eq_bot_of_affine]
  rfl

theorem supportLocalSpectrumMap_imageClosure (p : Spec (X.presheaf.stalk x))
    (hp : X.fromSpecStalk x p = irreducibleSetEquivPoints W) :
    CycleClass.Geometric.StratumClosure.integralImageClosure (supportLocalSpectrumMap X W x hx) = irreducibleSetEquivPoints.symm p := by
  apply irreducibleSetEquivPoints.injective
  rw [Integral.ClosedImage.BundleCycles.integralClosedImage_genericPoint, supportLocalSpectrumMap_genericPoint,
    irreducibleSetEquivPoints.apply_symm_apply]
  apply PrimeSpectrum.ext
  exact StalkSupportKernel.BundleCycles.supportLocalStalkMap_kernel X W x hx p hp

def supportStalkSpectrumIso (p : Spec (X.presheaf.stalk x))
    (hp : X.fromSpecStalk x p = irreducibleSetEquivPoints W) :
    Spec ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (StalkSupportKernel.BundleCycles.supportLocalPoint X W x hx)) ≅
      CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm p) :=
  Integral.ClosedImage.BundleCycles.integralClosedImageIso (supportLocalSpectrumMap X W x hx) ≪≫
    eqToIso (congrArg CycleClass.Geometric.GenericPoint.reducedSupportScheme (supportLocalSpectrumMap_imageClosure X W x hx p hp))

omit W x hx in
theorem reducedSupportInclusion_eqToHom {W W' : IrreducibleCloseds X} (h : W = W') :
    eqToHom (congrArg CycleClass.Geometric.GenericPoint.reducedSupportScheme h) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W' = CycleClass.Geometric.GenericPoint.reducedSupportι W := by
  subst W'
  exact Category.id_comp _

theorem supportStalkSpectrumIso_inclusion (p : Spec (X.presheaf.stalk x))
    (hp : X.fromSpecStalk x p = irreducibleSetEquivPoints W) :
    (supportStalkSpectrumIso X W x hx p hp).hom ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm p) =
      supportLocalSpectrumMap X W x hx := by
  unfold supportStalkSpectrumIso
  rw [Iso.trans_hom, eqToIso.hom, Category.assoc,
    reducedSupportInclusion_eqToHom (Spec (X.presheaf.stalk x))
      (supportLocalSpectrumMap_imageClosure X W x hx p hp),
    Integral.ClosedImage.BundleCycles.integralClosedImageIso_inclusion]

end

/-!
# LineBundleCycles: the constructed prime-support map factors through the support stalk
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme) (x : X) (p : Spec (X.presheaf.stalk x))

abbrev stalkPrimeGlobalSupport : IrreducibleCloseds X :=
  irreducibleSetEquivPoints.symm (X.fromSpecStalk x p)

theorem stalkPrimeGlobalSupport_mem : x ∈ (stalkPrimeGlobalSupport X x p : Set X) := by
  have h : X.fromSpecStalk x p ⤳ x :=
    ((IsLocalRing.specializes_closedPoint p).map (X.fromSpecStalk x).continuous).trans
      (specializes_of_eq Scheme.fromSpecStalk_closedPoint)
  exact h.mem_closed (stalkPrimeGlobalSupport X x p).isClosed (subset_closure (Set.mem_singleton _))

def stalkPrimeSupportIso :
    Spec ((CycleClass.Geometric.GenericPoint.reducedSupportScheme (stalkPrimeGlobalSupport X x p)).presheaf.stalk
      (StalkSupportKernel.BundleCycles.supportLocalPoint X (stalkPrimeGlobalSupport X x p) x (stalkPrimeGlobalSupport_mem X x p))) ≅
      CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm p) :=
  supportStalkSpectrumIso X (stalkPrimeGlobalSupport X x p) x (stalkPrimeGlobalSupport_mem X x p) p
    (irreducibleSetEquivPoints.apply_symm_apply _).symm

variable [AlgebraicGeometry.IsNoetherian X]

theorem stalkPrimeSupportIso_map :
    (stalkPrimeSupportIso X x p).hom ≫ Point.SupportMap.BundleCycles.pointSupportMap (X.fromSpecStalk x) p =
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme (stalkPrimeGlobalSupport X x p)).fromSpecStalk
        (StalkSupportKernel.BundleCycles.supportLocalPoint X (stalkPrimeGlobalSupport X x p) x (stalkPrimeGlobalSupport_mem X x p)) := by
  let W := stalkPrimeGlobalSupport X x p
  let hx := stalkPrimeGlobalSupport_mem X x p
  let hp := (irreducibleSetEquivPoints.apply_symm_apply (X.fromSpecStalk x p)).symm
  apply (cancel_mono (CycleClass.Geometric.GenericPoint.reducedSupportι W)).mp
  rw [Category.assoc, Point.SupportMap.BundleCycles.pointSupportMap_inclusion, ← Category.assoc]
  change ((supportStalkSpectrumIso X W x hx p hp).hom ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm p)) ≫
    X.fromSpecStalk x = _
  rw [supportStalkSpectrumIso_inclusion]
  exact StalkSupportKernel.BundleCycles.stalkMap_point_square X (CycleClass.Geometric.GenericPoint.reducedSupportι W) (StalkSupportKernel.BundleCycles.supportLocalPoint X W x hx) x
    (StalkSupportKernel.BundleCycles.supportLocalPoint_spec X W x hx)

theorem pointSupportMap_fromSpecStalk_factorization :
    Point.SupportMap.BundleCycles.pointSupportMap (X.fromSpecStalk x) p =
      (stalkPrimeSupportIso X x p).inv ≫
        (CycleClass.Geometric.GenericPoint.reducedSupportScheme (stalkPrimeGlobalSupport X x p)).fromSpecStalk
          (StalkSupportKernel.BundleCycles.supportLocalPoint X (stalkPrimeGlobalSupport X x p) x (stalkPrimeGlobalSupport_mem X x p)) := by
  rw [← stalkPrimeSupportIso_map X x p, Iso.inv_hom_id_assoc]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.StalkPrimeSupport.BundleCycles
