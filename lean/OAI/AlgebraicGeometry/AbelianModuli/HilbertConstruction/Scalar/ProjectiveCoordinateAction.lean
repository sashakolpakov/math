import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.CoordinateProjectivePoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.EvaluationCoordinateTransform
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.SectionLinearCoordinateAction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeneratingSectionFrameChanges

/-! # Projective Coordinate Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.ProjectiveCoordinateAction

noncomputable section

/-! The projective automorphism with the contragredient coefficient
matrix acts on actual scalar-coordinate sections by the prescribed
linear point-coordinate map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (S : Scheme.{u})

def scalarCoefficientEvaluation :
    (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor (RingHom.id Γ(S, ⊤))).obj (Line.Bundles.structureModule S) →ₗ[Γ(S, ⊤)] Γ(S, ⊤) where
  toFun v := Frame.Coordinates.structureModuleEndValue S
    ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (RingHom.id Γ(S, ⊤)) (Line.Bundles.structureModule S)).symm v)
  map_add' v w := by rw [map_add, map_add]
  map_smul' r v := by
    have he : (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (RingHom.id Γ(S, ⊤)) (Line.Bundles.structureModule S)).symm (r • v) =
        SectionValues.scalarSection r ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (RingHom.id Γ(S, ⊤)) (Line.Bundles.structureModule S)).symm v) := by
      apply (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (RingHom.id Γ(S, ⊤)) (Line.Bundles.structureModule S)).injective
      rw [AddEquiv.apply_symm_apply]
      have h := Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv_scalar (RingHom.id Γ(S, ⊤)) (Line.Bundles.structureModule S) r
        ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (RingHom.id Γ(S, ⊤)) (Line.Bundles.structureModule S)).symm v)
      simpa only [RingHom.id_apply, AddEquiv.apply_symm_apply] using h.symm
    rw [he]
    exact SectionValues.scalarSection_globalValue (M := Line.Bundles.structureModule S) r
      ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (RingHom.id Γ(S, ⊤)) (Line.Bundles.structureModule S)).symm v)

theorem scalarCoefficientEvaluation_section (a : End (Line.Bundles.structureModule S)) :
    scalarCoefficientEvaluation S
      (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (RingHom.id Γ(S, ⊤)) (Line.Bundles.structureModule S) a) =
        Frame.Coordinates.structureModuleEndValue S a := by
  change Frame.Coordinates.structureModuleEndValue S
    ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (RingHom.id Γ(S, ⊤)) (Line.Bundles.structureModule S)).symm
      (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (RingHom.id Γ(S, ⊤)) (Line.Bundles.structureModule S) a)) = _
  rw [AddEquiv.symm_apply_apply]

theorem scalarCoordinateSections_transform {n : ℕ}
    (v : Fin (n + 1) → Γ(S, ⊤))
    (T : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤))) :
    Section.CoefficientTransformations.transformSectionFamily (RingHom.id Γ(S, ⊤)) (Line.Bundles.structureModule S) (Family.SectionProjectiveCoordinates.scalarCoordinateSections v)
        (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap = Family.SectionProjectiveCoordinates.scalarCoordinateSections (T v) := by
  have hv : (fun i => scalarCoefficientEvaluation S
      (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (RingHom.id Γ(S, ⊤)) (Line.Bundles.structureModule S)
        (Family.SectionProjectiveCoordinates.scalarCoordinateSections v i))) = v := by
    funext i
    rw [scalarCoefficientEvaluation_section]
    exact (Global.Sections.structureModuleEndRingEquiv S).apply_symm_apply (v i)
  funext i
  apply Global.Sections.structureModuleEndValue_injective S
  have h := Section.EvaluationCoordinateTransform.transformedSectionEvaluation (RingHom.id Γ(S, ⊤)) (Line.Bundles.structureModule S)
    (Family.SectionProjectiveCoordinates.scalarCoordinateSections v) (scalarCoefficientEvaluation S) T i
  rw [hv, scalarCoefficientEvaluation_section] at h
  exact h.trans ((Global.Sections.structureModuleEndRingEquiv S).apply_symm_apply (T v i)).symm

theorem scalarCoordinateProjectivePoint_linear_action {n : ℕ}
    (v : Fin (n + 1) → Γ(S, ⊤))
    (T : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤)))
    (hv : ∀ x : S, ∃ i, x ∈ S.basicOpen (v i))
    (hT : ∀ x : S, ∃ i, x ∈ S.basicOpen (T v i)) :
    Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv ≫
        (Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).symm).hom =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (T v) hT := by
  let hs := Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover v hv
  let ht := GeneratingSectionFrameChanges.transformSectionFamily_covers (RingHom.id Γ(S, ⊤)) (Line.Bundles.LineBundle.trivial S)
    (Family.SectionProjectiveCoordinates.scalarCoordinateSections v) hs (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap
    (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).surjective
  have h := Relative.SectionLinearCoordinateAction.sectionProjectiveMorphism_linearCoordinateIso (𝟙 S) (Family.SectionProjectiveCoordinates.scalarCoordinateSections v) hs
    (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).symm ht
  exact h.trans (Section.ProjectiveTargetIso.sectionProjectiveMorphism_congr (𝟙 S) (scalarCoordinateSections_transform S v T)
    ht (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover (T v) hT))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.ProjectiveCoordinateAction
