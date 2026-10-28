import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Triple Spectrum Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TripleSpectrumComposition

/-! A composite of three affine base morphisms is the spectrum map of the composite ring map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem tripleSpectrumComposition {A B C D : CommRingCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : A ⟶ D) (hk : f ≫ g ≫ h = k) :
    (Spec.map h ≫ Spec.map g) ≫ Spec.map f = Spec.map k := by
  rw [← Spec.map_comp, ← Spec.map_comp, hk]

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TripleSpectrumComposition
