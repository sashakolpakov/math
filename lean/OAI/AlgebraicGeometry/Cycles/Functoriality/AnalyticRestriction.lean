import OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion
import Mathlib.Topology.LocalAtTarget

/-! # Analytic Restriction -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.AnalyticRestriction.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- An open subscheme with its original complex structure morphism. -/
def openSchemeOver (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (U.ι ≫ X.hom)

/-- The inclusion of the open subscheme over the complex base. -/
def openSchemeInclusion (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) : openSchemeOver X U ⟶ X :=
  Over.homMk U.ι rfl

instance (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) :
    IsOpenImmersion (openSchemeInclusion X U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- Restrict an actual complex morphism to a target open subscheme. -/
def restrictedSchemeMap {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (U : Y.left.Opens) :
    openSchemeOver X (f.left ⁻¹ᵁ U) ⟶ openSchemeOver Y U :=
  Over.homMk (f.left ∣_ U) (by
    change (f.left ∣_ U) ≫ (U.ι ≫ Y.hom) = (f.left ⁻¹ᵁ U).ι ≫ X.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w f])

theorem restrictedSchemeMap_inclusion {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ Y) (U : Y.left.Opens) :
    restrictedSchemeMap f U ≫ openSchemeInclusion Y U =
      openSchemeInclusion X (f.left ⁻¹ᵁ U) ≫ f := by
  apply Over.OverMorphism.ext
  exact morphismRestrict_ι f.left U

/-- The actual analytic open subset corresponding to an open subscheme. -/
def schemeAnalyticOpen (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) :
    Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (U : Set X.left),
    U.isOpen.preimage ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_underlying⟩

/-- Native points of the open subscheme are the genuine analytic open subspace. -/
def openSchemePointHomeomorph (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (openSchemeOver X U) ≃ₜ schemeAnalyticOpen X U :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.openImmersionPointHomeomorph (openSchemeInclusion X U)).trans
    (Homeomorph.setCongr (by
      change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range U.ι =
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (U : Set X.left)
      rw [Scheme.Opens.range_ι]))

theorem openSchemePointHomeomorph_val (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (openSchemeOver X U)) :
    (openSchemePointHomeomorph X U x).val =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openSchemeInclusion X U) x := rfl

/-- Analytic preimages agree with the inverse images of algebraic opens. -/
theorem schemeAnalyticOpen_preimage {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ Y) (U : Y.left.Opens) :
    (schemeAnalyticOpen X (f.left ⁻¹ᵁ U) : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (schemeAnalyticOpen Y U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) := rfl

/-- The analytic realization of restriction is proper whenever the
original analytic point map is proper. -/
theorem restrictedSchemeMap_isProperMap {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ Y) (hf : IsProperMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)) (U : Y.left.Opens) :
    IsProperMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (restrictedSchemeMap f U)) := by
  let eX := openSchemePointHomeomorph X (f.left ⁻¹ᵁ U)
  let eY := openSchemePointHomeomorph Y U
  let F := (schemeAnalyticOpen Y U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)).restrictPreimage
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
  have hF : IsProperMap F := hf.restrictPreimage _
  have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (restrictedSchemeMap f U) = eY.symm ∘ F ∘ eX := by
    funext x
    apply eY.injective
    rw [Function.comp_apply, Homeomorph.apply_symm_apply]
    apply Subtype.ext
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openSchemeInclusion Y U)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (restrictedSchemeMap f U) x) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openSchemeInclusion X (f.left ⁻¹ᵁ U)) x)
    rw [← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, ← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp,
      restrictedSchemeMap_inclusion]
  rw [he]
  exact eY.symm.isProperMap.comp (hF.comp eX.isProperMap)

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.AnalyticRestriction.Construction
