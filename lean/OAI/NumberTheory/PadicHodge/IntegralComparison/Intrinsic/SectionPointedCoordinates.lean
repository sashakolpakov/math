import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionReductionEvaluation

/-! # Section Pointed Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionPointedCoordinates

noncomputable section

/-! The actual reduced section lies in every reduced neighborhood,
and its evaluation is unchanged by identifying equal open subsets. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R S : Type u} [CommRing R] [CommRing S] (ρ : R →+* S)
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (sX : Spec (CommRingCat.of R) ⟶ X.left)
  (sY : Spec (CommRingCat.of S) ⟶ Y.left)
  (h : sY ≫ f = Spec.map (CommRingCat.ofHom ρ) ≫ sX)
  (U : X.left.Opens) (hU : ⊤ ≤ sX ⁻¹ᵁ U)

include h hU in
theorem contains : ⊤ ≤ sY ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  have he := congrArg (fun g : Spec (CommRingCat.of S) ⟶ X.left => g ⁻¹ᵁ U) h
  change sY ⁻¹ᵁ (f ⁻¹ᵁ U) = (Spec.map (CommRingCat.ofHom ρ)) ⁻¹ᵁ (sX ⁻¹ᵁ U) at he
  rw [he, top_unique hU]
  simp

end

namespace IntrinsicEvaluation

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)
  (U V : X.left.Opens) (h : U = V) (hU : ⊤ ≤ s ⁻¹ᵁ U) (hV : ⊤ ≤ s ⁻¹ᵁ V)

theorem transport (a : SmoothClosedSections.ring R X U) :
    SectionEvaluation.evaluation R X s hs V hV
      (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map (eqToHom h.symm).op).hom a) =
      SectionEvaluation.evaluation R X s hs U hU a :=
  SectionEvaluation.restriction R X s hs U hU V h.symm.le hV a

end IntrinsicEvaluation

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionPointedCoordinates
