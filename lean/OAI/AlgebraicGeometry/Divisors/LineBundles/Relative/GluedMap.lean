import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties

/-! # Glued Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.GluedMap.BundleCycles

noncomputable section

/-! A compatible natural transformation between actual relative gluing
diagrams induces a scheme map with the expected pullback charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (d e : (directedCover X).RelativeGluingData)
    (η : d.functor ⟶ e.functor)

instance relativeGluingData_isLocallyDirected (a : (directedCover X).RelativeGluingData) :
    (a.functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

def relativeGluedMapCocone : Cocone d.functor where
  pt := e.glued
  ι := η ≫ (colimit.cocone e.functor).ι

def relativeGluedMap : d.glued ⟶ e.glued :=
  colimit.desc _ (relativeGluedMapCocone d e η)

theorem relativeGluedMap_on_chart (U : X.AffineZariskiSite) :
    d.cover.f U ≫ relativeGluedMap d e η = η.app U ≫ e.cover.f U :=
  colimit.ι_desc (relativeGluedMapCocone d e η) U

variable (hη : η ≫ e.natTrans = d.natTrans)

include hη in
theorem relativeGluedMap_toBase : relativeGluedMap d e η ≫ e.toBase = d.toBase := by
  apply d.cover.hom_ext
  intro U
  have hs := d.ι_toBase U
  have ht := e.ι_toBase U
  have hq : η.app U ≫ e.natTrans.app U = d.natTrans.app U :=
    congrArg (fun t => t.app U) hη
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ e.toBase) (relativeGluedMap_on_chart d e η U)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => η.app U ≫ k) ht).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k => k ≫ (directedCover X).f U) hq).trans hs.symm)))))

include hη in
theorem relativeGluedMap_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback (η.app U) (d.cover.f U) (e.cover.f U) (relativeGluedMap d e η) := by
  have h := d.isPullback_natTrans_ι_toBase U
  have hq : η.app U ≫ e.natTrans.app U = d.natTrans.app U :=
    congrArg (fun t => t.app U) hη
  rw [← hq, ← relativeGluedMap_toBase d e η hη] at h
  exact h.of_right (relativeGluedMap_on_chart d e η U).symm (e.isPullback_natTrans_ι_toBase U)

include hη in
theorem relativeGluedMap_morphismProperty (P : MorphismProperty Scheme.{0})
    [IsZariskiLocalAtTarget P] (hP : ∀ U, P (η.app U)) : P (relativeGluedMap d e η) :=
  Global.DeformationProperties.BundleCycles.morphismProperty_of_cover_pullbacks P (relativeGluedMap d e η) e.cover d.cover.X d.cover.f
    (fun U => η.app U) (relativeGluedMap_chart_isPullback d e η hη) hP

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.GluedMap.BundleCycles
