import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPullbackId

/-! # Picard Normalization Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardNormalizationEq.Construction.PicardNormalization

noncomputable section

/-! Normalizing a family of line bundles along a section of its structure morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

/-- Remove the line bundle induced from the restriction to the section. -/
def normalize (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X :=
  q / PicardPullbackId.Construction.PicardPullback.map f (PicardPullbackId.Construction.PicardPullback.map e q)

include he

theorem section_pullback (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass S) :
    PicardPullbackId.Construction.PicardPullback.map e (PicardPullbackId.Construction.PicardPullback.map f q) = q := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q) = q
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, he, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]

theorem pullback_injective : Function.Injective (PicardPullbackId.Construction.PicardPullback.map f) := by
  intro q r h
  have h' := congrArg (PicardPullbackId.Construction.PicardPullback.map e) h
  rwa [section_pullback f e he, section_pullback f e he] at h'

theorem restriction_normalize (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    PicardPullbackId.Construction.PicardPullback.map e (normalize f e q) = 1 := by
  rw [normalize, map_div, section_pullback f e he]
  exact div_self' _

theorem normalize_pullback (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass S) :
    normalize f e (PicardPullbackId.Construction.PicardPullback.map f q) = 1 := by
  rw [normalize, section_pullback f e he]
  exact div_self' _

theorem normalize_eq_one_iff (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    normalize f e q = 1 ↔ ∃ r, PicardPullbackId.Construction.PicardPullback.map f r = q := by
  constructor
  · intro h
    exact ⟨PicardPullbackId.Construction.PicardPullback.map e q, (div_eq_one.mp h).symm⟩
  · rintro ⟨r, rfl⟩
    exact normalize_pullback f e he r

omit he in
/-- The class decomposition determines both the normalized part and the part
pulled back from the base. -/
theorem decompose (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    normalize f e q * PicardPullbackId.Construction.PicardPullback.map f (PicardPullbackId.Construction.PicardPullback.map e q) = q :=
  div_mul_cancel q _

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardNormalizationEq.Construction.PicardNormalization
