import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Spectrum Product Open Cover -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpectrumProductOpenCover

noncomputable section

/-! The two factors of a product ring form an explicit affine open cover
of its spectrum. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def spectrumProductOpenCover (A B : CommRingCat.{u}) :
    (Spec (CommRingCat.of (A × B))).OpenCover where
  I₀ := Bool
  X | false => Spec A | true => Spec B
  f | false => Spec.map (CommRingCat.ofHom (RingHom.fst A B))
    | true => Spec.map (CommRingCat.ofHom (RingHom.snd A B))
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      obtain ⟨z, rfl⟩ := (coprodSpec A B).surjective x
      obtain ⟨z, rfl⟩ := (coprodMk (Spec A) (Spec B)).surjective z
      rcases z with a | b
      · refine ⟨false, a, ?_⟩
        rw [coprodMk_inl, ← Scheme.Hom.comp_apply, coprodSpec_inl]
      · refine ⟨true, b, ?_⟩
        rw [coprodMk_inr, ← Scheme.Hom.comp_apply, coprodSpec_inr]
    · intro i
      cases i
      · rw [← coprodSpec_inl]
        infer_instance
      · rw [← coprodSpec_inr]
        infer_instance

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpectrumProductOpenCover
