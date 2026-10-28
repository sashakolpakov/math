import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportConditions
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PointComplements

/-! # Fiber Principal Support -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FiberPrincipalSupport

noncomputable section

/-! The original ambient principal parameters cover the complement of
the whole finite fiber. On the selected component their support is
exactly the original source section, giving the actual candidate data. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Cover
variable {Y X Z : Scheme.{0}} (f : Y ⟶ X) (i : X ⟶ Z) [IsAffineHom i]
  (U : Z.Opens) (hU : IsAffineOpen U) (I : X.IdealSheafData)
  {g : ℕ} (t : Fin g → Γ(Z,U))
  (ht : Ideal.span (Set.range (fun j => i.app U (t j))) = I.ideal ⟨i ⁻¹ᵁ U,hU.preimage i⟩)

include ht in
theorem cover : (f ≫ i) ⁻¹ᵁ U ⊓ (f ⁻¹ᵁ SectionIdealPuncturedCover.outside I) =
    ⨆ j, (f ≫ i) ⁻¹ᵁ Z.basicOpen (t j) := by
  change f ⁻¹ᵁ (i ⁻¹ᵁ U) ⊓ (f ⁻¹ᵁ SectionIdealPuncturedCover.outside I) = _
  rw [← Scheme.Hom.preimage_inf, SectionIdealPuncturedCover.cover I (i ⁻¹ᵁ U)
    (hU.preimage i) (fun j => i.app U (t j)) ht, Scheme.Hom.preimage_iSup]
  congr 1
  funext j
  rw [← Scheme.preimage_basicOpen]
  rfl
end Cover

variable (R : Type) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) [Y.left.IsSeparated]
  (f : Y ⟶ X) [IsFinite f.left] [Etale f.left]
  {Z : Scheme.{0}} (i : X.left ⟶ Z) [IsClosedImmersion i]
  (s : Spec (CommRingCat.of R) ⟶ Y.left) (hs : s ≫ Y.hom = 𝟙 _)
  [IsClosedImmersion s] [IsClosedImmersion (s ≫ f.left)]
  (U : Z.Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ (s ≫ f.left) ⁻¹ᵁ (i ⁻¹ᵁ U))
  (hgood : FiniteEtale.TraceBasis.Good R Y X f (i ⁻¹ᵁ U))

local instance sourceAlgebra : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X (i ⁻¹ᵁ U)) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))) :=
  AffineOpen.DeRhamTrace.sectionAlgebra R Y X f (i ⁻¹ᵁ U)

variable (z : IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ (i ⁻¹ᵁ U)))
  (hz : letI : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X (i ⁻¹ᵁ U)) R :=
      SectionEvaluation.quotientAlgebra R X Y f s hs (i ⁻¹ᵁ U) hcontains
    ((1 : R) ⊗ₜ[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X (i ⁻¹ᵁ U)] z :
      R ⊗[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X (i ⁻¹ᵁ U)] IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ (i ⁻¹ᵁ U))) =
        FiniteEtale.PointParameterKernel.component R X Y f s hs (i ⁻¹ᵁ U) (hU.preimage i) hcontains)
  {g : ℕ} (t : Fin g → Γ(Z,U))
  (ht : Ideal.span (Set.range (fun j => i.app U (t j))) =
    (s ≫ f.left).ker.ideal ⟨i ⁻¹ᵁ U,hU.preimage i⟩)

include hgood hz ht in
theorem conditions : Principal.InjectiveIntegerRows.SingleSupportedCandidate.Conditions
    (PrincipalSource.OpenReindex.wideOpens (f.left ≫ i) U hU)
    (PrincipalSource.OpenReindex.geometricOpens (f.left ≫ i) U hU (Y.left.basicOpen z))
    (PrincipalPoint.Fraction.family U t)
    (f.left ⁻¹ᵁ SectionIdealPuncturedCover.outside (s ≫ f.left).ker)
    (SectionIdealPuncturedCover.outside s.ker) := by
  apply PrincipalSource.SupportConditions.conditions (f.left ≫ i) U hU
    (Y.left.basicOpen z) (Y.left.basicOpen_le z) t ((hU.preimage i).preimage f.left |>.basicOpen z)
    (f.left ⁻¹ᵁ SectionIdealPuncturedCover.outside (s ≫ f.left).ker)
    (SectionIdealPuncturedCover.outside s.ker)
  · exact FiniteEtale.PointComplements.outside_le f.left s
  · exact FiniteEtale.PointComplements.selected_intersection R X Y f s hs
      (i ⁻¹ᵁ U) (hU.preimage i) hcontains hgood z hz (fun j => i.app U (t j)) ht
  · exact FiniteEtale.PointComplements.selected_global R X Y f s hs
      (i ⁻¹ᵁ U) (hU.preimage i) hcontains hgood z hz
  · exact FiniteEtale.PointComplements.fiber_global R X Y f s
      (i ⁻¹ᵁ U) hcontains
  · exact cover f.left i U hU (s ≫ f.left).ker t ht

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FiberPrincipalSupport
