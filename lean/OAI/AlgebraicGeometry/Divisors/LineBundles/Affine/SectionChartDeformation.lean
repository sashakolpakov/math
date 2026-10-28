import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionDeformationSmooth
import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.AffineRingMaps
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties

/-! # Section Chart Deformation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionChartDeformation.BundleCycles

noncomputable section

/-! Smoothness of the genuine deformation rings on compatible affine
section charts, with their original section-ring coefficient map. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineSectionChart_deformation_smooth {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (p : Y ⟶ X) [Smooth p] (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)
    (U : Y.Opens) (V : X.Opens) (hUaff : IsAffineOpen U) (hVaff : IsAffineOpen V)
    (hV : V ≤ s ⁻¹ᵁ U) (hU : U ≤ p ⁻¹ᵁ V) :
    letI := (p.appLE V U hU).hom.toAlgebra
    Algebra.Smooth Γ(X, V) (Deformation.Iff.BundleCycles.deformationAlgebra (s.ker.ideal ⟨U, hUaff⟩)) := by
  let := (p.appLE V U hU).hom.toAlgebra
  let := (s.appLE U V hV).hom.toAlgebra
  let : IsScalarTower Γ(X, V) Γ(Y, U) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (ConcreteCategory.congr_hom (Section.AffineRingMaps.BundleCycles.section_appLE_retraction p s hs U V hV hU) a).symm
  let : Algebra.Smooth Γ(X, V) Γ(Y, U) := p.smooth_appLE hVaff hUaff hU
  let : IsNoetherianRing Γ(X, V) := Global.DeformationProperties.BundleCycles.affineBaseRing_noetherian ⟨V, hVaff⟩
  let : IsNoetherianRing Γ(Y, U) := Global.DeformationProperties.BundleCycles.affineBaseRing_noetherian ⟨U, hUaff⟩
  have h := SectionDeformationSmooth.BundleCycles.affineSection_deformation_smooth Γ(X, V) Γ(Y, U)
  have he := Section.AffineRingMaps.BundleCycles.section_appLE_kernel p s hs U V hV hU hUaff
  exact he ▸ h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionChartDeformation.BundleCycles
