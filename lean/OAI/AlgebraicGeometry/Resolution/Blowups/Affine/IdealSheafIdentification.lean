import OAI.AlgebraicGeometry.Resolution.Blowups.Open.IdealSheafBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.QuotientBaseChange

/-! # Ideal Sheaf Identification -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealSheafIdentification.Construction

noncomputable section

/-! Identifying the pullback of an ideal sheaf to an affine chart with its actual quotient kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- The native affine quotient chart of the closed center is the actual
pullback along the corresponding affine chart of the ambient scheme. -/
theorem idealSheaf_subscheme_affine_isPullback (I : X.IdealSheafData) (U : X.affineOpens) :
    IsPullback (I.subschemeCover.f U)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))))
      I.subschemeι U.2.fromSpec := by
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.openCover.map_prop U
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · rw [Scheme.IdealSheafData.subschemeCover_map_subschemeι]
    change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫ U.2.isoSpec.inv) ≫ U.1.ι = _
    rw [Category.assoc]
    rfl
  · exact (congrArg (fun W : X.Opens => I.subschemeι ⁻¹ᵁ W) U.2.opensRange_fromSpec).trans
      (I.opensRange_subschemeCover_map U).symm

/-- The ideal sheaf on an affine chart is exactly the kernel of the
quotient by its original affine ideal. -/
theorem idealSheaf_comap_fromSpec_eq_quotient_kernel (I : X.IdealSheafData) (U : X.affineOpens) :
    I.comap U.2.fromSpec = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)))).ker := by
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have h := Open.IdealSheafBaseChange.Construction.kernel_comap_of_open_pullback I.subschemeι
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))))
    (I.subschemeCover.f U) U.2.fromSpec (idealSheaf_subscheme_affine_isPullback I U).flip
  rwa [Scheme.IdealSheafData.ker_subschemeι] at h

/-- On every affine morphism over an original chart, the pulled-back ideal
is the kernel of the quotient by the actual extended affine ideal. -/
theorem idealSheaf_comap_affineMap_eq_quotient_kernel (I : X.IdealSheafData) (U : X.affineOpens)
    {S : Type u} [CommRing S] (φ : Γ(X, U) →+* S) :
    I.comap (Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I.ideal U).map φ)))).ker := by
  let : Algebra Γ(X, U) S := φ.toAlgebra
  rw [Scheme.IdealSheafData.comap_comp, idealSheaf_comap_fromSpec_eq_quotient_kernel]
  exact QuotientBaseChange.Construction.affineQuotient_kernel_comap (S := S) (I.ideal U)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealSheafIdentification.Construction
