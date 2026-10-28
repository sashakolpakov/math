import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.AffineNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionPrincipalSupport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionCompositeEvaluation

/-! # Section Principal Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.SectionPrincipalNeighborhood

noncomputable section

/-! A neighborhood of a section on a closed subscheme can be reached
by a principal refinement in the original ambient affine chart. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] [IsArtinianRing R] [IsLocalRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (i : X ⟶ Y) [IsClosedImmersion i.left]
  (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)
  (U : Y.left.Opens) (hUa : IsAffineOpen U) (hU : ⊤ ≤ s ⁻¹ᵁ (i.left ⁻¹ᵁ U))
  (V : X.left.Opens) (hV : ⊤ ≤ s ⁻¹ᵁ V)

include hs hUa hU hV in
theorem exists_principal : ∃ r : Γ(Y.left,U),
    (⊤ ≤ s ⁻¹ᵁ (i.left ⁻¹ᵁ Y.left.basicOpen r)) ∧ i.left ⁻¹ᵁ Y.left.basicOpen r ≤ V := by
  let : Subsingleton (Spec (CommRingCat.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  let p : Spec (CommRingCat.of R) := Classical.ofNonempty
  have hpU : i.left (s p) ∈ U := hU (show p ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
  have hpV : s p ∈ V := hV (show p ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
  obtain ⟨W,_,hpW,_,hWV⟩ := AffineNeighborhood.exists_subopen i.left U V (s p) hpU hpV
  have hW : ⊤ ≤ (s ≫ i.left) ⁻¹ᵁ W := by
    intro q _
    have hqp : q = p := Subsingleton.elim _ _
    subst q
    exact hpW
  let hsY := Intrinsic.SectionCompositeEvaluation.over_base R X Y i s hs
  obtain ⟨r,hr,hrW⟩ := Intrinsic.SectionPrincipalSupport.exists_normalized
    R Y (s ≫ i.left) hsY U hU hUa W hW
  exact ⟨r,Intrinsic.SectionEvaluation.principal_contains R Y (s ≫ i.left) hsY U hU r hr,
    (i.left.preimage_mono hrW).trans hWV⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.SectionPrincipalNeighborhood
