import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionChartDeformation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.PuncturedLaurentChart

/-! # Deformation Chart Smooth -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Section.DeformationChartSmooth.BundleCycles

noncomputable section

/-! The actual global deformation chart over a compatible smooth-section
neighborhood is smooth over the section's base scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem sectionDeformationChart_smooth {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (p : Y ⟶ X) [Smooth p] (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)
    (U : Y.Opens) (V : X.Opens) (hUaff : IsAffineOpen U) (hVaff : IsAffineOpen V)
    (hV : V ≤ s ⁻¹ᵁ U) (hU : U ≤ p ⁻¹ᵁ V) :
    Smooth ((Global.Deformation.BundleCycles.globalDeformationCover s.ker).f ⟨U, hUaff⟩ ≫
      (Global.Deformation.BundleCycles.globalDeformationProjection s.ker ≫ p)) := by
  let := (p.appLE V U hU).hom.toAlgebra
  let I := s.ker.ideal ⟨U, hUaff⟩
  let : Algebra.Smooth Γ(X, V) (Deformation.Iff.BundleCycles.deformationAlgebra I) :=
    Affine.SectionChartDeformation.BundleCycles.affineSectionChart_deformation_smooth p s hs U V hUaff hVaff hV hU
  let a : Γ(X, V) ⟶ CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I) :=
    CommRingCat.ofHom (algebraMap Γ(X, V) (Deformation.Iff.BundleCycles.deformationAlgebra I))
  let ha : Smooth (Spec.map a) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have hmap : p.appLE V U hU ≫
      CommRingCat.ofHom (algebraMap Γ(Y, U) (Deformation.Iff.BundleCycles.deformationAlgebra I)) = a := by
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq Γ(X, V) Γ(Y, U) (Deformation.Iff.BundleCycles.deformationAlgebra I)).symm
  have he : (Global.Deformation.BundleCycles.globalDeformationCover s.ker).f ⟨U, hUaff⟩ ≫
      (Global.Deformation.BundleCycles.globalDeformationProjection s.ker ≫ p) = Spec.map a ≫ hVaff.fromSpec := by
    have hc := Global.PuncturedLaurentChart.BundleCycles.globalDeformationChart_toBase s.ker (⟨U, hUaff⟩ : Y.AffineZariskiSite)
    rw [← Category.assoc]
    calc
      _ = (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (Deformation.Iff.BundleCycles.deformationAlgebra I))) ≫
          hUaff.fromSpec) ≫ p := congrArg (fun k => k ≫ p) hc
      _ = Spec.map a ≫ hVaff.fromSpec := by
        rw [Category.assoc,
      ← IsAffineOpen.SpecMap_appLE_fromSpec p hVaff hUaff hU,
      ← Category.assoc, ← Spec.map_comp, hmap]
  rw [he]
  have hv : Smooth hVaff.fromSpec := inferInstance
  exact @AlgebraicGeometry.smooth_comp _ _ (Spec.map a) _ hVaff.fromSpec ha hv

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Section.DeformationChartSmooth.BundleCycles
