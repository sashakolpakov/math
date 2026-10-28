import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CechConstants

/-! # Cech Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CechEvaluation.Construction

noncomputable section

/-! Evaluation along a base section splits the actual Cech constants
over any coefficient ring, including rings with nilpotents. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

def sectionEvaluationRingHom (V : X.Opens) (hV : ⊤ ≤ σ ⁻¹ᵁ V) : Γ(X, V) →+* R :=
  (σ.appLE V ⊤ hV ≫ (Scheme.ΓSpecIso (.of R)).hom).hom

include hσ in
set_option backward.isDefEq.respectTransparency false in
theorem sectionEvaluation_constants (V : X.Opens) (hV : ⊤ ≤ σ ⁻¹ᵁ V) (r : R) :
    sectionEvaluationRingHom σ V hV (FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f V r) = r := by
  change (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ V (by simp)) ≫
    (σ.appLE V ⊤ hV ≫ (Scheme.ΓSpecIso (.of R)).hom)) r = r
  rw [Category.assoc, ← Category.assoc (f.appLE ⊤ V _), Scheme.Hom.appLE_comp_appLE, hσ]
  simp [Scheme.Hom.appLE]

include hσ in
set_option backward.isDefEq.respectTransparency false in
def sectionEvaluationLinearMap (V : X.Opens) (hV : ⊤ ≤ σ ⁻¹ᵁ V) :
    (FormalGeometry.Completion.RelativeStructureSections.Construction.relativeStructureSections f).obj (op V) →ₗ[R] R where
  toFun := sectionEvaluationRingHom σ V hV
  map_add' := map_add _
  map_smul' r s := by
    change sectionEvaluationRingHom σ V hV (FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f V r * (show Γ(X, V) from s)) =
      r * sectionEvaluationRingHom σ V hV s
    rw [map_mul, sectionEvaluation_constants f σ hσ]

variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0)
  (ha : ⊤ ≤ σ ⁻¹ᵁ (∏ᶜ fun k : Fin 1 => U (a.val k)))

include hσ in
def relativeCechEvaluation : (FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X 0 →ₗ[R] R :=
  (sectionEvaluationLinearMap f σ hσ _ ha).comp
    ((Pi.π (FormalGeometry.Completion.RelativeCechTerms.Construction.relativeCechFactor f U 0) a).hom.comp (FormalGeometry.Completion.RelativeCechTerms.Construction.relativeStructureCechTermIso f U 0).hom.hom)

theorem relativeCechEvaluation_constants (hU : iSup U = ⊤) :
    (relativeCechEvaluation f σ hσ U a ha).comp (CechConstants.Construction.relativeCechConstants f U hU) = LinearMap.id := by
  apply LinearMap.ext
  intro r
  change sectionEvaluationRingHom σ _ ha
    (Pi.π (FormalGeometry.Completion.RelativeCechTerms.Construction.relativeCechFactor f U 0) a
      ((FormalGeometry.Completion.RelativeCechTerms.Construction.relativeStructureCechTermIso f U 0).hom (CechConstants.Construction.relativeCechConstants f U hU r))) = r
  rw [CechConstants.Construction.relativeCechConstants_coordinate]
  exact sectionEvaluation_constants f σ hσ _ ha r

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CechEvaluation.Construction
