import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Smooth Closed Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

noncomputable section

/-! Smooth affine sections and the quotient of a closed immersion use
the original coefficient algebra of the de Rham forms. The quotient
identification is the actual pullback of functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (R : Type u) [CommRing R]

abbrev ring (X : Over (Spec (CommRingCat.of R))) (U : X.left.Opens) : CommAlgCat.{u} R :=
  (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op U)

theorem smooth_sections (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom]
    (U : Y.left.Opens) (hU : IsAffineOpen U) : Algebra.Smooth R (ring R Y U) := by
  have h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (ring R Y U)))) := by
    rw [← AffineOpen.SectionBase.overBase R Y U hU]
    infer_instance
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp h)

variable (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsClosedImmersion f.left] (U : Y.left.Opens) (hU : IsAffineOpen U)

def quotientEquiv :
    (ring R Y U ⧸ f.left.ker.ideal ⟨U, hU⟩) ≃ₐ[R] ring R X (f.left ⁻¹ᵁ U) :=
  (Ideal.quotientEquivAlgOfEq R (f.left.ker_apply ⟨U, hU⟩)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sectionPullback f U)
      (f.left.app_surjective U hU))

@[simp]
theorem quotientEquiv_mk (a : ring R Y U) :
    quotientEquiv R X Y f U hU (Ideal.Quotient.mk (f.left.ker.ideal ⟨U, hU⟩) a) =
      f.left.app U a := rfl

theorem smooth_quotient [Smooth X.hom] :
    Algebra.Smooth R (ring R Y U ⧸ f.left.ker.ideal ⟨U, hU⟩) := by
  let := smooth_sections R X (f.left ⁻¹ᵁ U) (hU.preimage f.left)
  exact Algebra.Smooth.of_equiv (quotientEquiv R X Y f U hU).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections
