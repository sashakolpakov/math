import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PuncturedDeformation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ChowLocalization

/-! # Punctured Laurent Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.PuncturedLaurentChart.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual Laurent charts inside the global deformation
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.AffineZariskiSite)

def globalPuncturedLaurentChart : Spec (CommRingCat.of (LaurentPolynomial Γ(X, U.1))) ⟶ Deformation.BundleCycles.globalDeformation I :=
  Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap (I.ideal U) ≫ (Deformation.BundleCycles.globalDeformationCover I).f U

instance globalPuncturedLaurentChart_openImmersion : IsOpenImmersion (globalPuncturedLaurentChart I U) := by
  exact @IsOpenImmersion.comp _ _ _
    (show Spec (CommRingCat.of (LaurentPolynomial Γ(X, U.1))) ⟶ (Deformation.BundleCycles.globalDeformationCover I).X U from
      Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap (I.ideal U)) ((Deformation.BundleCycles.globalDeformationCover I).f U)
    (Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap_openImmersion (I.ideal U)) ((Deformation.BundleCycles.globalDeformationCover I).map_prop U)

theorem globalDeformationChart_toBase :
    (Deformation.BundleCycles.globalDeformationCover I).f U ≫ Deformation.BundleCycles.globalDeformationProjection I =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))) ≫ U.2.fromSpec := by
  have h := (Deformation.BundleCycles.globalDeformation_chart_isPullback I U).w.symm
  exact h

theorem globalPuncturedLaurentChart_toBase :
    globalPuncturedLaurentChart I U ≫ Deformation.BundleCycles.globalDeformationProjection I =
      Laurent.FiberGenericPoint.BundleCycles.laurentProjection Γ(X, U.1) ≫ U.2.fromSpec := by
  let l : Spec (CommRingCat.of (LaurentPolynomial Γ(X, U.1))) ⟶ (Deformation.BundleCycles.globalDeformationCover I).X U :=
    Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap (I.ideal U)
  let b := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U))))
  exact (Category.assoc l ((Deformation.BundleCycles.globalDeformationCover I).f U) (Deformation.BundleCycles.globalDeformationProjection I)).trans
    ((congrArg (fun k : (Deformation.BundleCycles.globalDeformationCover I).X U ⟶ X => l ≫ k)
      (globalDeformationChart_toBase I U)).trans
      ((Category.assoc l b U.2.fromSpec).symm.trans
        (congrArg (fun k : Spec (CommRingCat.of (LaurentPolynomial Γ(X, U.1))) ⟶ Spec Γ(X, U.1) =>
          k ≫ U.2.fromSpec) (Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap_toBase (I.ideal U)))))

theorem globalPuncturedLaurentChart_range :
    Set.range (globalPuncturedLaurentChart I U) =
      (Set.range ((Deformation.BundleCycles.globalDeformationCover I).f U)) ∩ (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I : Set (Deformation.BundleCycles.globalDeformation I)) := by
  have hb := Scheme.preimage_basicOpen_top ((Deformation.BundleCycles.globalDeformationCover I).f U)
    (Specialization.BundleCycles.globalDeformationParameterSection I)
  rw [Specialization.BundleCycles.globalDeformationParameterSection_on_chart] at hb
  have ha : Set.range (Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap (I.ideal U)) =
      ((Deformation.BundleCycles.globalDeformationCover I).f U) ⁻¹' (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I : Set (Deformation.BundleCycles.globalDeformation I)) :=
    (Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap_range (I.ideal U)).trans
      (congrArg (fun V : ((Deformation.BundleCycles.globalDeformationCover I).X U).Opens => (V : Set ((Deformation.BundleCycles.globalDeformationCover I).X U))) hb).symm
  let c : (Deformation.BundleCycles.globalDeformationCover I).X U → Deformation.BundleCycles.globalDeformation I := (Deformation.BundleCycles.globalDeformationCover I).f U
  let l : Spec (CommRingCat.of (LaurentPolynomial Γ(X, U.1))) → (Deformation.BundleCycles.globalDeformationCover I).X U :=
    Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap (I.ideal U)
  exact (Set.range_comp c l).trans ((congrArg (Set.image c) ha).trans
    (Set.image_preimage_eq_range_inter))

theorem globalPuncturedLaurentChart_range_subset :
    Set.range (globalPuncturedLaurentChart I U) ⊆ Set.range (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) := by
  rw [globalPuncturedLaurentChart_range]
  exact fun _ hx => (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I).range_ι.symm ▸ hx.2

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.PuncturedLaurentChart.BundleCycles
