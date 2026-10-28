import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSectionRatioSubring
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectivePresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.CoefficientRecovery

/-! # Ratio Field Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.RatioFieldCoordinates

noncomputable section

/-! Section ratios record precisely where a section vanishes on a
denominator chart. For a field base, the generating condition for these
ratios can be expressed over the field itself. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {X : Scheme.{u}} {M : X.Modules}

theorem sectionRatio_basicOpen (s t : Line.Bundles.structureModule X ⟶ M) :
    (Ample.LineBundles.sectionNonvanishing s).toScheme.basicOpen (Frames.sectionRatio s t) =
      (Ample.LineBundles.sectionNonvanishing s).ι ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing t := by
  rw [Frame.Coordinates.sectionRatio_eq_frameCoordinate, ← Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate,
    Nonvanishing.sectionNonvanishing_pullback]

theorem sectionRatio_coefficientDifference (p : X ⟶ Spec (.of K))
    (s t : Line.Bundles.structureModule X ⟶ M) (c : K) :
    Frames.sectionRatio s (t - Coefficient.ScalarSections.coefficientScalarSection p c s) =
      Frames.sectionRatio s t - Coefficient.ModulePresheaf.schemeCoefficientMap ((Ample.LineBundles.sectionNonvanishing s).ι ≫ p) c := by
  change BasisSectionRatioSubring.sectionRatioAddHom s (t - Coefficient.ScalarSections.coefficientScalarSection p c s) = _
  rw [map_sub]
  change Frames.sectionRatio s t - Frames.sectionRatio s (Coefficient.ScalarSections.coefficientScalarSection p c s) = _
  rw [BasisSectionRatioSubring.sectionRatio_coefficientScalar, Frames.sectionRatio_self, mul_one]

private theorem adjoin_top_of_base_map {R S A : Type*}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R A] [Algebra S A]
    (ρ : R →+* S) (hρ : ∀ r, algebraMap S A (ρ r) = algebraMap R A r)
    (s : Set A) (hs : Algebra.adjoin R s = ⊤) : Algebra.adjoin S s = ⊤ := by
  let C := Algebra.adjoin S s
  let D : Subalgebra R A :=
    { __ := C.toSubring
      algebraMap_mem' := fun r => hρ r ▸ C.algebraMap_mem (ρ r) }
  have hD : Algebra.adjoin R s ≤ D :=
    Algebra.adjoin_le (fun x hx => Algebra.subset_adjoin (R := S) hx)
  rw [hs] at hD
  apply top_unique
  intro x _
  exact hD (show x ∈ (⊤ : Subalgebra R A) from trivial)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectivePresentation.SectionRatiosGenerate.overField (p : X ⟶ Spec (.of K)) {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M)) (hs : ProjectivePresentation.SectionRatiosGenerate p s)
    (i : Fin (n + 1)) :
    let := (Coefficient.ModulePresheaf.schemeCoefficientMap ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ p)).toAlgebra;
    Algebra.adjoin K (Set.range fun j => Frames.sectionRatio (s i) (s j)) = ⊤ := by
  let U := Ample.LineBundles.sectionNonvanishing (s i)
  let q := U.ι ≫ p
  let := (Coefficient.ModulePresheaf.schemeCoefficientMap q).toAlgebra
  let := q.appTop.hom.toAlgebra
  exact adjoin_top_of_base_map (Scheme.ΓSpecIso (.of K)).hom.hom
    (fun r => DFunLike.congr_fun (ProjectiveChart.CoefficientRecovery.schemeCoefficientMap_comp_specGlobalIso q) r)
    (Set.range fun j => Frames.sectionRatio (s i) (s j)) (hs i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.RatioFieldCoordinates
