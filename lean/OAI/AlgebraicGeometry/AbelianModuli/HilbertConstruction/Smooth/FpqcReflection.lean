import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Fpqc Reflection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FpqcReflection

noncomputable section

/-! Smoothness is reflected by actual Cartesian recovery along a surjective flat quasi-compact base map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem smooth_of_isPullback_fpqc
    {X Y S T : Scheme.{u}} (q : Y ⟶ X) (p : Y ⟶ T) (f : X ⟶ S) (c : T ⟶ S)
    (h : IsPullback q p f c) [Surjective c] [Flat c] [QuasiCompact c] [Smooth p] : Smooth f :=
  MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FpqcReflection
