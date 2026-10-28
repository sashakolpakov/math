import OAI.AlgebraicGeometry.CycleClass.Thom.SpecSupportKernel
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SupportCoordinates

/-! # Support Prime -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SupportPrime.Constructions

noncomputable section

/-! The affine prime of a genuine irreducible support and its precise
localized stalk kernel in the chosen actual affine coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.StalkCoordinates OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalStalk.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SupportCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SpecSupportKernel.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : CommRingCat) (X : Scheme) (e : X ≅ Spec R) (A : IrreducibleCloseds X)

def coordinateSupport : IrreducibleCloseds (Spec R) := irreducibleSetEquivPoints.symm (e.hom (IntersectionGeometry.supportPoint A))

theorem coordinateSupport_genericPoint : IntersectionGeometry.supportPoint (coordinateSupport R X e A) = e.hom (IntersectionGeometry.supportPoint A) :=
  irreducibleSetEquivPoints.apply_symm_apply _

theorem coordinateSupport_coe : (coordinateSupport R X e A : Set (Spec R)) = e.inv ⁻¹' (A : Set X) := by
  have h := e.inv.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image ({e.hom (IntersectionGeometry.supportPoint A)} : Set (Spec R))
  rw [Set.image_singleton] at h
  have he : e.inv (e.hom (IntersectionGeometry.supportPoint A)) = IntersectionGeometry.supportPoint A :=
    congrArg (fun f : X ⟶ X => f (IntersectionGeometry.supportPoint A)) e.hom_inv_id
  rw [he] at h
  exact h.trans (congrArg (fun S : Set X => e.inv ⁻¹' S)
    (A.isIrreducible.isGenericPoint_genericPoint A.isClosed))

theorem coordinateSupport_mem (x : X) (hx : x ∈ (A : Set X)) : e.hom x ∈ (coordinateSupport R X e A : Set (Spec R)) := by
  rw [coordinateSupport_coe]
  change e.inv (e.hom x) ∈ (A : Set X)
  have he : e.inv (e.hom x) = x := congrArg (fun f : X ⟶ X => f x) e.hom_inv_id
  rw [he]
  exact hx

theorem support_preimage_zeroLocus :
    (A : Set X) = e.hom ⁻¹' PrimeSpectrum.zeroLocus ((e.hom (IntersectionGeometry.supportPoint A)).asIdeal : Set R) := by
  have h := SpecSupportKernel.Constructions.support_coe R (coordinateSupport R X e A)
  rw [coordinateSupport_genericPoint] at h
  rw [← h, coordinateSupport_coe, ← Set.preimage_comp]
  have he : (e.inv ∘ e.hom : X → X) = id :=
    congrArg (fun f : X ⟶ X => (f : X → X)) e.hom_inv_id
  rw [he]
  rfl

theorem coordinate_support_kernel (x : X) (hx : x ∈ (A : Set X)) :
    (StalkPrimeQuotient.Constructions.kernelPrime X A x hx).asIdeal.map (ProductIs.Constructions.StalkCoordinates.stalkCoordinateIso R X e x).hom.hom =
      (e.hom (IntersectionGeometry.supportPoint A)).asIdeal.map (algebraMap R (Localization.AtPrime (e.hom x).asIdeal)) := by
  have h := SupportCoordinates.Constructions.kernelPrime_coordinates R X e A (coordinateSupport R X e A)
    (coordinateSupport_genericPoint R X e A).symm x hx (e.hom x) rfl (coordinateSupport_mem R X e A x hx)
  have hs := SpecSupportKernel.Constructions.support_kernel R (coordinateSupport R X e A) (e.hom x) (coordinateSupport_mem R X e A x hx)
  rw [coordinateSupport_genericPoint] at hs
  exact h.trans hs

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SupportPrime.Constructions
