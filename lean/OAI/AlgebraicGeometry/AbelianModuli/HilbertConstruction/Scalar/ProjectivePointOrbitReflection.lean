import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.ProjectiveCoordinateAction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveMorphismBundleComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.ProjectiveTransport

/-! # Projective Point Orbit Reflection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.ProjectivePointOrbitReflection

noncomputable section

/-! Equality of scalar-coordinate projective points reflects an actual
unit multiple. An invertible change of the coefficient module therefore
reflects a common linear change and independent unit multiples of an
ordered configuration, over any base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v

section Coordinates
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]

/-- The dual pairing converts a coefficient-module automorphism into
an automorphism of point coordinates. -/
def coefficientCoordinatePointTransform
    (C : (ι →₀ R) ≃ₗ[R] (ι →₀ R)) : (ι → R) ≃ₗ[R] (ι → R) :=
  (Finsupp.llift R R R ι).trans
    (C.dualMap.trans (Finsupp.llift R R R ι).symm)

theorem coefficientCoordinatePointTransform_coefficient
    (C : (ι →₀ R) ≃ₗ[R] (ι →₀ R)) :
    Dual.CoordinateTransform.pointCoordinateCoefficientTransform (coefficientCoordinatePointTransform C) = C := by
  apply LinearEquiv.ext
  intro a
  apply (Module.evalEquiv R (ι →₀ R)).injective
  apply LinearMap.ext
  intro φ
  change φ (Dual.CoordinateTransform.pointCoordinateCoefficientTransform
    (coefficientCoordinatePointTransform C) a) = φ (C a)
  rw [Dual.CoordinateTransform.pointCoordinateCoefficientTransform_pairing]
  simp only [Dual.CoordinateTransform.pointCoordinateDualTransform, coefficientCoordinatePointTransform,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.dualMap_apply]

end Coordinates

variable {S : Scheme.{u}} {n : ℕ}

private theorem structureEndValue_comp (f g : End (Line.Bundles.structureModule S)) :
    Global.Sections.structureModuleEndRingEquiv S (f ≫ g) =
      Global.Sections.structureModuleEndRingEquiv S g * Global.Sections.structureModuleEndRingEquiv S f :=
  (Global.Sections.structureModuleEndRingEquiv S).map_mul g f

theorem scalarCoordinateProjectivePoint_eq_implies_unit_multiple
    (v w : Fin (n + 1) → Γ(S, ⊤))
    (hv : ∀ x : S, ∃ i, x ∈ S.basicOpen (v i))
    (hw : ∀ x : S, ∃ i, x ∈ S.basicOpen (w i))
    (h : Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint w hw) :
    ∃ a : Γ(S, ⊤)ˣ, w = (a : Γ(S, ⊤)) • v := by
  dsimp only [Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint] at h
  let e : Line.Bundles.structureModule S ≅ Line.Bundles.structureModule S :=
    Section.ProjectiveComparisonComponents.sameProjectiveMapBundleIso (𝟙 S) (Family.SectionProjectiveCoordinates.scalarCoordinateSections v)
      (Family.SectionProjectiveCoordinates.scalarCoordinateSections w) (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover v hv)
      (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover w hw) h
  have he : IsUnit (Global.Sections.structureModuleEndRingEquiv S e.hom) :=
    (Global.Sections.structureModuleEnd_isIso_iff e.hom).mp inferInstance
  refine ⟨he.unit, ?_⟩
  funext i
  have hc : Family.SectionProjectiveCoordinates.scalarCoordinateSections v i ≫ e.hom = Family.SectionProjectiveCoordinates.scalarCoordinateSections w i := by
    dsimp only [e, Section.ProjectiveComparisonComponents.sameProjectiveMapBundleIso]
    dsimp only [Section.ComparisonTransport.sectionComparisonIso]
    convert (Section.ProjectiveMorphismBundleComparison.sameProjectiveMapBundleIso_section (𝟙 S) (Family.SectionProjectiveCoordinates.scalarCoordinateSections v)
      (Family.SectionProjectiveCoordinates.scalarCoordinateSections w) (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover v hv)
      (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover w hw) h i) using 2 <;> rfl
  have hi := congrArg (Global.Sections.structureModuleEndRingEquiv S) hc
  rw [structureEndValue_comp] at hi
  simp only [Family.SectionProjectiveCoordinates.scalarCoordinateSections, RingEquiv.apply_symm_apply] at hi
  change w i = (he.unit : Γ(S, ⊤)) * v i
  rw [he.unit_spec]
  exact hi.symm

theorem scalarCoordinateProjectivePoint_linear_cover
    (v : Fin (n + 1) → Γ(S, ⊤))
    (T : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤)))
    (hv : ∀ x : S, ∃ i, x ∈ S.basicOpen (v i)) :
    ∀ x : S, ∃ i, x ∈ S.basicOpen (T v i) := by
  have h := GeneratingSectionFrameChanges.transformSectionFamily_covers (RingHom.id Γ(S, ⊤))
    (Line.Bundles.LineBundle.trivial S) (Family.SectionProjectiveCoordinates.scalarCoordinateSections v)
    (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover v hv)
    (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap
    (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).surjective
  change ∀ x : S, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing
    (Section.CoefficientTransformations.transformSectionFamily (RingHom.id Γ(S, ⊤)) (Line.Bundles.structureModule S) (Family.SectionProjectiveCoordinates.scalarCoordinateSections v)
      (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap i) at h
  rw [ProjectiveCoordinateAction.scalarCoordinateSections_transform S v T] at h
  intro x
  obtain ⟨i, hi⟩ := h x
  refine ⟨i, ?_⟩
  rw [Nonvanishing.sectionNonvanishing_scalar] at hi
  change x ∈ S.basicOpen (Global.Sections.structureModuleEndRingEquiv S
    ((Global.Sections.structureModuleEndRingEquiv S).symm (T v i))) at hi
  simpa only [Family.SectionProjectiveCoordinates.scalarCoordinateSections, RingEquiv.apply_symm_apply] using hi

/-- A projective coordinate change carrying all specified scalar points
gives the actual orbit relation used by the balanced quotient. -/
theorem configurationFrameRelated_of_projective_coordinate_change
    {κ : Type v} (v w : κ → Fin (n + 1) → Γ(S, ⊤))
    (hv : ∀ a, ∀ x : S, ∃ i, x ∈ S.basicOpen (v a i))
    (hw : ∀ a, ∀ x : S, ∃ i, x ∈ S.basicOpen (w a i))
    (C : (Fin (n + 1) →₀ Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) →₀ Γ(S, ⊤)))
    (h : ∀ a, Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (v a) (hv a) ≫
      (Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S C).hom =
        Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (w a) (hw a)) :
    Configuration.ProjectiveTransport.ConfigurationFrameRelated v w := by
  let T := coefficientCoordinatePointTransform C.symm
  have hT a : ∀ x : S, ∃ i, x ∈ S.basicOpen (T (v a) i) :=
    scalarCoordinateProjectivePoint_linear_cover (v a) T (hv a)
  have hp a : Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (T (v a)) (hT a) =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (w a) (hw a) := by
    have ha := ProjectiveCoordinateAction.scalarCoordinateProjectivePoint_linear_action S (v a) T (hv a) (hT a)
    have hC : (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).symm = C := by
      rw [coefficientCoordinatePointTransform_coefficient, LinearEquiv.symm_symm]
    rw [hC] at ha
    exact ha.symm.trans (h a)
  choose s hs using fun a =>
    scalarCoordinateProjectivePoint_eq_implies_unit_multiple (T (v a)) (w a)
      (hT a) (hw a) (hp a)
  exact ⟨T, s, hs⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.ProjectivePointOrbitReflection
