import OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.CycleSpecialization

/-! # Cone Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeNaturality.BundleCycles

noncomputable section

/-!
# LineBundleCycles: normal-cone fibers under coefficient maps

The parameter ideal maps to the parameter ideal, so the quotient square
is a pushout. Transporting along the proved normal-cone isomorphisms
gives the actual pullback square of affine cone inclusions.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u
variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f)

/-- The square of actual normal-cone quotient maps is a ring pushout. -/
theorem normalConeFiber_isPushout :
    IsPushout (CommRingCat.ofHom (Deformation.Maps.BundleCycles.deformationMap I J f hf))
      (CommRingCat.ofHom (Affine.Specialization.BundleCycles.normalConeFiberRingMap I))
      (CommRingCat.ofHom (Affine.Specialization.BundleCycles.normalConeFiberRingMap J))
      (CommRingCat.ofHom (R := Cone.BundleCycles.NormalConeRing I) (S := Cone.BundleCycles.NormalConeRing J) (Deformation.Maps.BundleCycles.normalConeMap I J f hf)) := by
  let a : CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I) ⟶ CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra J) :=
    CommRingCat.ofHom (Deformation.Maps.BundleCycles.deformationMap I J f hf)
  have h : IsPushout a (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I)))
      (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal J)))
      (CommRingCat.ofHom (R := SpecialFiber.BundleCycles.DeformationSpecialRing I) (S := SpecialFiber.BundleCycles.DeformationSpecialRing J)
        (Deformation.Maps.BundleCycles.deformationSpecialMap I J f hf)) :=
    QuotientFiber.BundleCycles.quotient_isPushout_of_map_eq a (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) (Deformation.Iff.BundleCycles.deformationSpecialIdeal J)
      (SpecialFiberLocalization.BundleCycles.deformationSpecialIdeal_map I J f hf)
  apply h.of_iso' (Iso.refl _) (Iso.refl _)
    (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I).toCommRingCatIso
    (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv J).toCommRingCatIso
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    change Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) p =
      SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I
        ((SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I).symm (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) p))
    exact (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I).apply_symm_apply _ |>.symm
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    change Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal J) p =
      SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv J
        ((SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv J).symm (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal J) p))
    exact (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv J).apply_symm_apply _ |>.symm
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    exact Deformation.Maps.BundleCycles.normalConeSpecialFiberEquiv_natural I J f hf p

/-- The normal-cone inclusion pulls back to the normal-cone inclusion after any coefficient map. -/
theorem normalConeFiber_isPullback :
    IsPullback (Affine.Specialization.BundleCycles.normalConeFiberInclusion J) (Spec.map
      (CommRingCat.ofHom (R := Cone.BundleCycles.NormalConeRing I) (S := Cone.BundleCycles.NormalConeRing J) (Deformation.Maps.BundleCycles.normalConeMap I J f hf)))
      (Spec.map (CommRingCat.ofHom (Deformation.Maps.BundleCycles.deformationMap I J f hf))) (Affine.Specialization.BundleCycles.normalConeFiberInclusion I) :=
  AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _ (normalConeFiber_isPushout I J f hf)

/-- In particular, the cone of a closed support is the actual pulled-back zero fiber. -/
theorem closedSupportNormalCone_isPullback (Q : Ideal R) :
    IsPullback (Affine.Specialization.BundleCycles.normalConeFiberInclusion (I.map (Ideal.Quotient.mk Q)))
      (CycleSpecialization.BundleCycles.closedSupportNormalConeInclusion I Q) (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationInclusion I Q)
      (Affine.Specialization.BundleCycles.normalConeFiberInclusion I) :=
  normalConeFiber_isPullback I (I.map (Ideal.Quotient.mk Q)) (Ideal.Quotient.mk Q)
    (fun _ hx => Ideal.mem_map_of_mem _ hx)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeNaturality.BundleCycles
