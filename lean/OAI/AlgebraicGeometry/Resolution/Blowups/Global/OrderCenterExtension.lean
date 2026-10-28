import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedGlobalCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderLocusPreservation
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialSheafRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.SchemeImage
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PointedSmoothCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialFiltration

/-! # Order Center Extension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderCenterExtension.Construction

noncomputable section

/-! A permissible center on an open containing the entire order locus extends to an actual global smooth center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem differential_order_support_ne_univ
    {X : Scheme} [IsIntegral X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J : X.IdealSheafData) (hJ : J ≠ ⊥) (n : ℕ) :
    ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support : Set X) ≠ Set.univ := by
  intro h
  have hs : (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support = ⊤ := SetLike.coe_injective h
  have hz := Scheme.IdealSheafData.support_eq_top_iff.mp hs
  have hle := DifferentialFiltration.Construction.smoothDifferentialIdealSheaf_monotone_order f J (Nat.zero_le n)
  rw [Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_zero, hz] at hle
  exact hJ (le_bot_iff.mp hle)

theorem local_permissible_center_range_in_order_support
    {V X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (j : V ⟶ X) [IsOpenImmersion j]
    (J : X.IdealSheafData) (L : V.IdealSheafData) (n : ℕ)
    (hp : J.comap j ≤ L ^ (n + 1)) :
    Set.range (L.subschemeι ≫ j) ⊆ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support := by
  have hle := OrderLocusPreservation.Construction.global_tangent_le_permissible_center (j ≫ f) (J.comap j) L n hp
  have hs := Scheme.IdealSheafData.support_antitone hle
  rw [← Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open f J n j, Scheme.IdealSheafData.support_comap] at hs
  rintro x ⟨z, rfl⟩
  exact hs z.property

abbrev openCenterExtension {V X : Scheme} (j : V ⟶ X) (L : V.IdealSheafData) : X.IdealSheafData :=
  (L.subschemeι ≫ j).ker

theorem order_supported_center_closedImmersion
    {V X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (j : V ⟶ X) [IsOpenImmersion j]
    (J : X.IdealSheafData) (L : V.IdealSheafData) (n : ℕ)
    (hp : J.comap j ≤ L ^ (n + 1))
    (hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support : Set X) ⊆ Set.range j) :
    IsClosedImmersion (L.subschemeι ≫ j) :=
  SupportedGlobalCenter.Construction.supported_center_composite_isClosedImmersion L.subschemeι j _
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support.isClosed
    (local_permissible_center_range_in_order_support f j J L n hp) hcover

theorem order_supported_center_extension_restrict
    {V X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (j : V ⟶ X) [IsOpenImmersion j]
    (J : X.IdealSheafData) (L : V.IdealSheafData) (n : ℕ)
    (hp : J.comap j ≤ L ^ (n + 1))
    (hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support : Set X) ⊆ Set.range j) :
    (openCenterExtension j L).comap j = L := by
  have h := SupportedGlobalCenter.Construction.supported_center_kernel_comap L.subschemeι j _
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support.isClosed
    (local_permissible_center_range_in_order_support f j J L n hp) hcover
  rw [Scheme.IdealSheafData.ker_subschemeι] at h
  exact h

theorem order_supported_center_extension_nonzero
    {V X : Scheme} [IsIntegral X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (j : V ⟶ X) [IsOpenImmersion j] (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    (L : V.IdealSheafData) (n : ℕ) (hp : J.comap j ≤ L ^ (n + 1))
    (hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support : Set X) ⊆ Set.range j) :
    openCenterExtension j L ≠ ⊥ :=
  SupportedGlobalCenter.Construction.supported_center_kernel_ne_bot L.subschemeι j _
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support.isClosed
    (local_permissible_center_range_in_order_support f j J L n hp) hcover
    (differential_order_support_ne_univ f J hJ n)

theorem order_supported_center_extension_smooth
    {V X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (j : V ⟶ X) [IsOpenImmersion j]
    (J : X.IdealSheafData) (L : V.IdealSheafData) (n : ℕ)
    [Smooth (L.subschemeι ≫ (j ≫ f))] (hp : J.comap j ≤ L ^ (n + 1))
    (hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support : Set X) ⊆ Set.range j) :
    Smooth ((openCenterExtension j L).subschemeι ≫ f) := by
  let : IsClosedImmersion (L.subschemeι ≫ j) := order_supported_center_closedImmersion f j J L n hp hcover
  let : Smooth ((L.subschemeι ≫ j) ≫ f) := by rw [Category.assoc]; infer_instance
  exact PointedSmoothCenter.Construction.kernel_subscheme_smooth_of_closed_immersion (L.subschemeι ≫ j) f

theorem order_supported_center_extension_permissible
    {V X : Scheme} [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (j : V ⟶ X) [IsOpenImmersion j] (J : X.IdealSheafData) (L : V.IdealSheafData) (n : ℕ)
    [Smooth (L.subschemeι ≫ (j ≫ f))] (hp : J.comap j ≤ L ^ (n + 1))
    (hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support : Set X) ⊆ Set.range j) :
    J ≤ openCenterExtension j L ^ (n + 1) := by
  let : Smooth ((openCenterExtension j L).subschemeι ≫ f) :=
    order_supported_center_extension_smooth f j J L n hp hcover
  apply (SmoothCenterCriterion.Construction.smooth_global_center_permissible_iff_support f (openCenterExtension j L) J n).mpr
  have hs := SupportedGlobalCenter.Construction.supported_center_kernel_support L.subschemeι j _
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support.isClosed
    (local_permissible_center_range_in_order_support f j J L n hp) hcover
  intro x hx
  exact local_permissible_center_range_in_order_support f j J L n hp (hs ▸ hx)

theorem order_supported_center_extension_integral
    {V X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (j : V ⟶ X) [IsOpenImmersion j]
    (J : X.IdealSheafData) (L : V.IdealSheafData) (n : ℕ) [IsIntegral L.subscheme]
    (hp : J.comap j ≤ L ^ (n + 1))
    (hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support : Set X) ⊆ Set.range j) :
    IsIntegral (openCenterExtension j L).subscheme := by
  let : IsClosedImmersion (L.subschemeι ≫ j) := order_supported_center_closedImmersion f j J L n hp hcover
  exact Integral.SchemeImage.Construction.scheme_image_isIntegral (L.subschemeι ≫ j)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderCenterExtension.Construction
