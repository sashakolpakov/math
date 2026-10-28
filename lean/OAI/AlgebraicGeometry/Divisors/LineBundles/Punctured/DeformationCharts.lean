import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.PuncturedLaurentChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.LiftRange

/-! # Deformation Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DeformationCharts.BundleCycles

noncomputable section

/-!
# LineBundleCycles: Laurent charts cover the actual punctured global deformation
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def puncturedDeformationProjection : Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I ⟶ X :=
  Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I ≫ Global.Deformation.BundleCycles.globalDeformationProjection I

def puncturedLaurentChart (U : X.AffineZariskiSite) :
    Spec (CommRingCat.of (LaurentPolynomial Γ(X, U.1))) ⟶ Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I :=
  IsOpenImmersion.lift (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) (Global.PuncturedLaurentChart.BundleCycles.globalPuncturedLaurentChart I U)
    (Global.PuncturedLaurentChart.BundleCycles.globalPuncturedLaurentChart_range_subset I U)

theorem puncturedLaurentChart_inclusion (U : X.AffineZariskiSite) :
    puncturedLaurentChart I U ≫ Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I = Global.PuncturedLaurentChart.BundleCycles.globalPuncturedLaurentChart I U :=
  IsOpenImmersion.lift_fac _ _ _

instance puncturedLaurentChart_openImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion (puncturedLaurentChart I U) := by
  have h : IsOpenImmersion (puncturedLaurentChart I U ≫ Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) :=
    (congrArg (fun f => IsOpenImmersion f) (puncturedLaurentChart_inclusion I U)).mpr inferInstance
  exact IsOpenImmersion.of_comp (puncturedLaurentChart I U) (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I)

theorem puncturedLaurentChart_toBase (U : X.AffineZariskiSite) :
    puncturedLaurentChart I U ≫ puncturedDeformationProjection I =
      Laurent.FiberGenericPoint.BundleCycles.laurentProjection Γ(X, U.1) ≫ U.2.fromSpec := by
  rw [puncturedDeformationProjection, ← Category.assoc, puncturedLaurentChart_inclusion]
  exact Global.PuncturedLaurentChart.BundleCycles.globalPuncturedLaurentChart_toBase I U

theorem puncturedLaurentChart_range (U : X.AffineZariskiSite) :
    Set.range (puncturedLaurentChart I U) = puncturedDeformationProjection I ⁻¹' (U.1 : Set X) := by
  rw [Open.LiftRange.BundleCycles.range_openLift (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) (Global.PuncturedLaurentChart.BundleCycles.globalPuncturedLaurentChart I U)
    (puncturedLaurentChart I U) (puncturedLaurentChart_inclusion I U),
    Global.PuncturedLaurentChart.BundleCycles.globalPuncturedLaurentChart_range, Set.preimage_inter]
  have hopen : (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) ⁻¹'
      (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I : Set (Global.Deformation.BundleCycles.globalDeformation I)) = Set.univ := by
    change (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I).ι ⁻¹' (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I : Set (Global.Deformation.BundleCycles.globalDeformation I)) = _
    rw [← (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I).range_ι, Set.preimage_range]
    rfl
  rw [hopen, Set.inter_univ]
  exact congrArg (Set.preimage (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I))
    (congrArg (fun V : (Global.Deformation.BundleCycles.globalDeformation I).Opens => (V : Set (Global.Deformation.BundleCycles.globalDeformation I)))
      (Global.DeformationProperties.BundleCycles.globalDeformationProjection_preimage I U)).symm

theorem puncturedLaurentChart_covers (x : Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I) :
    ∃ U : X.AffineZariskiSite, x ∈ Set.range (puncturedLaurentChart I U) := by
  let U := (directedCover X).idx (puncturedDeformationProjection I x)
  refine ⟨U, ?_⟩
  rw [puncturedLaurentChart_range]
  obtain ⟨y, hy⟩ := (directedCover X).covers (puncturedDeformationProjection I x)
  change puncturedDeformationProjection I x ∈ U.1
  exact hy ▸ y.property

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DeformationCharts.BundleCycles
