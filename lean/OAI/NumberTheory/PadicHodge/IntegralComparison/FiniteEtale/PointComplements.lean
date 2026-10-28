import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PointParameterKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionIdealPuncturedCover

/-! # Point Complements -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PointComplements

noncomputable section

/-! The selected principal source open meets the full finite fiber in
exactly the original section. Its two actual punctured complements
therefore agree on that open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

section Schemes
variable {X Y T : Scheme.{u}} (f : Y ⟶ X) (s : T ⟶ Y) [IsClosedImmersion s]

theorem outside_le :
    f ⁻¹ᵁ SectionIdealPuncturedCover.outside (s ≫ f).ker ≤
      SectionIdealPuncturedCover.outside s.ker := by
  intro y hy
  change f y ∉ (s ≫ f).ker.support at hy
  change y ∉ s.ker.support
  intro hys
  change y ∈ (s.ker.support : Set Y) at hys
  rw [Scheme.Hom.support_ker, s.isClosedEmbedding.isClosed_range.closure_eq] at hys
  obtain ⟨a, rfl⟩ := hys
  exact hy ((s ≫ f).range_subset_ker_support ⟨a, rfl⟩)

variable (I : X.IdealSheafData) (U : X.Opens) (hU : IsAffineOpen U)
  {g : ℕ} (t : Fin g → Γ(X,U))
  (ht : Ideal.span (Set.range t) = I.ideal ⟨U,hU⟩)
  (z : Γ(Y,f ⁻¹ᵁ U))

include ht in
theorem principal_preimage :
    Y.basicOpen z ⊓ (f ⁻¹ᵁ SectionIdealPuncturedCover.outside I) =
      ⨆ j, Y.basicOpen (IdealSheafPrincipalEquations.sequence (f ⁻¹ᵁ U) z
        (fun k => f.app U (t k)) j) := by
  apply le_antisymm
  · intro y hy
    have hyU : f y ∈ U := Y.basicOpen_le z hy.1
    have hyI : f y ∈ U ⊓ SectionIdealPuncturedCover.outside I := ⟨hyU,hy.2⟩
    rw [SectionIdealPuncturedCover.cover I U hU t ht] at hyI
    obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hyI
    apply Opens.mem_iSup.mpr
    refine ⟨j, ?_⟩
    change y ∈ Y.basicOpen (Y.presheaf.map (homOfLE (Y.basicOpen_le z)).op (f.app U (t j)))
    rw [Scheme.basicOpen_res]
    refine ⟨hy.1, ?_⟩
    rw [← Scheme.preimage_basicOpen]
    exact hj
  · intro y hy
    obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hy
    change y ∈ Y.basicOpen (Y.presheaf.map (homOfLE (Y.basicOpen_le z)).op (f.app U (t j))) at hj
    rw [Scheme.basicOpen_res] at hj
    refine ⟨hj.1, ?_⟩
    have hp : f y ∈ X.basicOpen (t j) := by
      change y ∈ f ⁻¹ᵁ X.basicOpen (t j)
      rw [Scheme.preimage_basicOpen]
      exact hj.2
    exact SectionIdealPuncturedCover.basicOpen_le I U hU t ht j hp

variable (J : Y.IdealSheafData) (hV : IsAffineOpen (Y.basicOpen z))
  (hj : Ideal.span (Set.range (IdealSheafPrincipalEquations.sequence (f ⁻¹ᵁ U) z
    (fun k => f.app U (t k)))) = J.ideal ⟨Y.basicOpen z,hV⟩)

include ht hj in
theorem from_equations :
    Y.basicOpen z ⊓ (f ⁻¹ᵁ SectionIdealPuncturedCover.outside I) =
      Y.basicOpen z ⊓ SectionIdealPuncturedCover.outside J :=
  (principal_preimage f I U hU t ht z).trans
    (SectionIdealPuncturedCover.cover J (Y.basicOpen z) hV
      (IdealSheafPrincipalEquations.sequence (f ⁻¹ᵁ U) z (fun k => f.app U (t k))) hj).symm

end Schemes

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : Y ⟶ X) [IsFinite f.left] [Etale f.left]
  (s : Spec (CommRingCat.of R) ⟶ Y.left) (hs : s ≫ Y.hom = 𝟙 _)
  (U : X.left.Opens) (hUa : IsAffineOpen U) (hU : ⊤ ≤ (s ≫ f.left) ⁻¹ᵁ U)
  (hgood : TraceBasis.Good R Y X f U)

local instance sourceAlgebra : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) :=
  AffineOpen.DeRhamTrace.sectionAlgebra R Y X f U

variable (z : IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U))
  (hz : letI : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) R := Finite.SectionEvaluation.quotientAlgebra R X Y f s hs U hU
    ((1 : R) ⊗ₜ[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U] z : R ⊗[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U] IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) =
      PointParameterKernel.component R X Y f s hs U hUa hU)
  [IsClosedImmersion s] [IsClosedImmersion (s ≫ f.left)]
  {g : ℕ} (t : Fin g → IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)
  (ht : Ideal.span (Set.range t) = (s ≫ f.left).ker.ideal ⟨U,hUa⟩)

include hgood hz ht in
theorem selected_intersection :
    Y.left.basicOpen z ⊓ (f.left ⁻¹ᵁ SectionIdealPuncturedCover.outside (s ≫ f.left).ker) =
      Y.left.basicOpen z ⊓ SectionIdealPuncturedCover.outside s.ker := by
  exact from_equations f.left (s ≫ f.left).ker U hUa t ht z s.ker
    ((hUa.preimage f.left).basicOpen z)
    (PointParameterKernel.ideal R X Y f s hs U hUa hU hgood z hz t ht)

include hgood hz in
omit [IsClosedImmersion (s ≫ f.left)] in
theorem selected_global :
    Y.left.basicOpen z ⊔ SectionIdealPuncturedCover.outside s.ker = ⊤ :=
  SectionIdealPuncturedCover.section_global (Y.left.basicOpen z) s
    (PointParameterKernel.contains R X Y f s hs U hUa hU hgood z hz)

include hU in
omit [IsFinite f.left] [Etale f.left] [IsClosedImmersion s] in
theorem fiber_global :
    (f.left ⁻¹ᵁ U) ⊔ (f.left ⁻¹ᵁ SectionIdealPuncturedCover.outside (s ≫ f.left).ker) = ⊤ := by
  apply top_unique
  intro y _
  have hc := SectionIdealPuncturedCover.section_global U (s ≫ f.left) hU
  have hy : f.left y ∈ U ⊔ SectionIdealPuncturedCover.outside (s ≫ f.left).ker := by
    rw [hc]
    trivial
  exact hy

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PointComplements
