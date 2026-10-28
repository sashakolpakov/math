import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionKernel

/-! # Principal Section Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PrincipalSectionAlgebra

noncomputable section

/-! The literal section kernel localizes on a principal affine
neighborhood, using the native restriction algebra throughout. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {U V : X.left.Opens} (i : V ⟶ U) (hU : IsAffineOpen U)
  (a : SmoothClosedSections.ring R X U) (he : V = X.left.basicOpen a)

include hU he in
theorem localization : letI := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R X i
    IsLocalization.Away a (SmoothClosedSections.ring R X V) := by
  subst V
  exact hU.isLocalization_basicOpen a

variable (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)
  (hsU : ⊤ ≤ s ⁻¹ᵁ U) (hsV : ⊤ ≤ s ⁻¹ᵁ V)
  (I : Ideal (SmoothClosedSections.ring R X U))
  (hI : I ≤ RingHom.ker (SectionEvaluation.evaluation R X s hs U hsU).toRingHom)
  (ha : ∀ x, SectionEvaluation.evaluation R X s hs U hsU x = 0 → a * x ∈ I)

include hU he hI ha in
theorem kernel :
    RingHom.ker (SectionEvaluation.evaluation R X s hs V hsV).toRingHom =
      I.map (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op).hom.toRingHom) := by
  let := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R X i
  let := localization R X i hU a he
  apply Principal.SectionKernel.kernel a
    (SectionEvaluation.evaluation R X s hs U hsU).toRingHom
    (SectionEvaluation.evaluation R X s hs V hsV).toRingHom
    ?_ I hI ha
  apply RingHom.ext
  intro x
  exact SectionEvaluation.restriction R X s hs U hsU V i.le hsV x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PrincipalSectionAlgebra
