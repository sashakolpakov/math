import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.StrictTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.ResolutionGeometry

/-! # Strict Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.StrictTransform.Construction

noncomputable section

/-! Projectivity and birationality of actual integral scheme-image strict transforms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

def strictTransformProjectivePresentation {Y X : Scheme} (π : Y ⟶ X)
    (H : X.IdealSheafData) (U : X.Opens) [IsIso (π ∣_ U)]
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Y g) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation (Integral.StrictTransform.Construction.strictTransformIdeal π H U).subscheme
      ((Integral.StrictTransform.Construction.strictTransformIdeal π H U).subschemeι ≫ g) :=
  ClosedTransformProjectivity.Construction.closedSubschemeProjectivePresentation P (Integral.StrictTransform.Construction.strictTransformIdeal π H U)

theorem strictTransformToBase_partialIso {Y X : Scheme} (π : Y ⟶ X)
    (H : X.IdealSheafData) (U : X.Opens) [IsIso (π ∣_ U)]
    [NoetherianSpace H.subscheme] [IsIntegral H.subscheme]
    [Nonempty (H.subschemeι ⁻¹ᵁ U).toScheme] :
    ∃ e : (Integral.StrictTransform.Construction.strictTransformIdeal π H U).subscheme.PartialIso H.subscheme,
      e.source.ι ≫ Integral.StrictTransform.Construction.strictTransformToBase π H U = e.iso.hom ≫ e.target.ι := by
  let : IsIntegral (Integral.StrictTransform.Construction.strictTransformIdeal π H U).subscheme := Integral.StrictTransform.Construction.strictTransformIdeal_isIntegral π H U
  let : IsIso (Integral.StrictTransform.Construction.strictTransformToBase π H U ∣_ (H.subschemeι ⁻¹ᵁ U)) :=
    Integral.StrictTransform.Construction.strictTransformToBase_restrict_isIso π H U
  apply ResolutionGeometry.Construction.partialIso_of_isIso_restriction (Integral.StrictTransform.Construction.strictTransformToBase π H U) (H.subschemeι ⁻¹ᵁ U)
  exact (H.subschemeι ⁻¹ᵁ U).isOpen.dense (by
    obtain ⟨x⟩ := ‹Nonempty (H.subschemeι ⁻¹ᵁ U).toScheme›
    exact ⟨x.1, x.2⟩)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.StrictTransform.Construction
