import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingFunctorComparison

/-! # Nonvanishing Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange

noncomputable section

/-! Nonvanishing opens of line-bundle sections commute with arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem sectionNonvanishing_lineBundle_baseChange (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y)
    (s : Line.Bundles.structureModule Y ⟶ L.sheaf) :
    Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s) = f ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing s := by
  ext x
  change x ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s) ↔ f x ∈ Ample.LineBundles.sectionNonvanishing s
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyTrivial (f x)
  let y : (f ⁻¹ᵁ U).toScheme := ⟨x, hxU⟩
  have hc : Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection (f ⁻¹ᵁ U).ι (Ample.LineBundles.pullbackSection f s)) =
      Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection (f ∣_ U) (Ample.LineBundles.pullbackSection U.ι s)) :=
    (NonvanishingFunctorComparison.sectionNonvanishing_pullback_comp f (f ⁻¹ᵁ U).ι s).trans
      ((congrArg (fun k : (f ⁻¹ᵁ U).toScheme ⟶ Y => Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection k s))
        (morphismRestrict_ι f U).symm).trans
        (NonvanishingFunctorComparison.sectionNonvanishing_pullback_comp U.ι (f ∣_ U) s).symm)
  calc
    x ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s) ↔
        y ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection (f ⁻¹ᵁ U).ι (Ample.LineBundles.pullbackSection f s)) := by
      rw [Section.Nonvanishing.sectionNonvanishing_pullback (f ⁻¹ᵁ U).ι (Ample.LineBundles.pullbackSection f s)]
      rfl
    _ ↔ y ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection (f ∣_ U) (Ample.LineBundles.pullbackSection U.ι s)) :=
      (congrArg (fun V => y ∈ V) hc).to_iff
    _ ↔ (f ∣_ U) y ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection U.ι s) := by
      rw [Scalar.BaseChange.sectionNonvanishing_baseChange_of_frame (f ∣_ U) e.inv (Ample.LineBundles.pullbackSection U.ι s)]
      rfl
    _ ↔ f x ∈ Ample.LineBundles.sectionNonvanishing s := by
      rw [Section.Nonvanishing.sectionNonvanishing_pullback U.ι s]
      change ((f ∣_ U) ≫ U.ι) y ∈ Ample.LineBundles.sectionNonvanishing s ↔ f x ∈ Ample.LineBundles.sectionNonvanishing s
      rw [morphismRestrict_ι]
      rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange
