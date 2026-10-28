import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.RegularSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.FrameCoordinateUnits
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.IsoSpecSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationSectionMorphism

/-! # Section Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.SectionPullback

noncomputable section

/-! The right tensor inclusion on the actual fixed-fiber affine charts
is pullback of the original family sections. This identifies coordinate
units with the transition units of the pulled-back original frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

theorem regularSectionTransport_eq_map {X : Scheme.{0}} {U V : X.Opens}
    (h : U = V) (a : Γ(X, U)) :
    Regular.SectionTransport.regularSectionTransport h a = X.presheaf.map (eqToHom h.symm).op a := by
  subst V
  change a = X.presheaf.map (𝟙 _) a
  exact (ConcreteCategory.congr_hom (X.presheaf.map_id (Opposite.op U)) a).symm

variable (R k : Type) [CommRing R] [CommRing k] [Algebra R k]
    (X : Over (Spec (.of R)))

theorem fixedFiberRegularSectionEquiv_includeRight
    (V : X.left.affineOpens) (a : Family.AffineTangentLifts.familyAffineRing R X V) :
    RegularSections.fixedFiberRegularSectionEquiv R k X V ((1 : k) ⊗ₜ[R] a) =
      (CoordinateProjection.fixedFamilyProjection R k X).app V.1 (Family.FrameCoordinateUnits.familyAffineSectionEquiv R X V a) := by
  let B := Family.AffineTangentLifts.familyAffineRing R X V
  let C := k ⊗[R] B
  let f := CoordinateProjection.fixedFamilyProjection R k X
  let j : Spec (.of C) ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X).left :=
    (AffineDiagram.fixedFiberTensorInclusion R k X V).left
  let : IsOpenImmersion j := AffineDiagram.fixedFiberTensorInclusion_open R k X V
  let q : Spec (.of C) ⟶ V.1.toScheme :=
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[R] C).toRingHom) ≫
      (HilbertConstruction.Affine.OverChartPoints.affineOverIso R ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj V)).inv.left
  have hj : j.opensRange = CoordinateProjection.fixedFiberAffineOpen R k X V :=
    CoordinateProjection.fixedFiberTensorInclusion_range R k X V
  have hq : q ≫ V.1.ι = j ≫ f :=
    (Category.assoc
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] C).toRingHom))
      V.1.toScheme.isoSpec.inv V.1.ι).trans
        (CoordinateProjection.fixedFiberTensorInclusion_projection R k X V).symm
  have h : j.opensRange ≤ f ⁻¹ᵁ V.1.ι.opensRange := by
    rw [V.1.opensRange_ι, hj]
    exact le_rfl
  have hΓ : q.appTop a = (Scheme.ΓSpecIso (.of C)).inv ((1 : k) ⊗ₜ[R] a) := by
    change (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[R] C).toRingHom)).appTop
        (V.1.toScheme.isoSpec.inv.appTop a) = _
    rw [Affine.IsoSpecSections.affineIsoSpec_inv_appTop]
    exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[R] C).toRingHom)) a).symm
  have H := ConcreteCategory.congr_hom
    (Open.ImmersionSectionMorphism.openImmersionTopSectionIso_morphism q V.1.ι j f hq h) a
  change (IsOpenImmersion.ΓIsoTop j).hom (q.appTop a) =
    f.appLE V.1.ι.opensRange j.opensRange h ((IsOpenImmersion.ΓIsoTop V.1.ι).hom a) at H
  rw [hΓ] at H
  have hi : Regular.SectionTransport.regularSectionTransport V.1.opensRange_ι
      ((IsOpenImmersion.ΓIsoTop V.1.ι).hom a) = Family.FrameCoordinateUnits.familyAffineSectionEquiv R X V a := by
    rw [regularSectionTransport_eq_map]
    exact ConcreteCategory.congr_hom (Affine.IsoSpecSections.openInclusionTopSectionIso X.left V.1) a
  change Regular.SectionTransport.regularSectionTransport hj
    ((IsOpenImmersion.ΓIsoTop j).hom ((Scheme.ΓSpecIso (.of C)).inv ((1 : k) ⊗ₜ[R] a))) = _
  rw [H, Affine.PresentationSectionMorphism.regularSectionTransport_appLE f V.1.opensRange_ι hj h (show CoordinateProjection.fixedFiberAffineOpen R k X V ≤ f ⁻¹ᵁ V.1 from le_rfl), hi]
  exact ConcreteCategory.congr_hom (f.appLE_eq_app (U := V.1)) _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.SectionPullback
