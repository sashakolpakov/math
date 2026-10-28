import Mathlib.CategoryTheory.Iso

/-! # Chain Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.ChainComposition

/-! A short categorical composition identity for actual frame comparisons. -/

open _root_.CategoryTheory

theorem frameChain_composition {C : Type*} [Category C] {A B D E F G H I : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (d : E ≅ F) (e : F ≅ G)
    (t : B ≅ H) (s : H ≅ E) (a' : A ≅ I) (b' : I ≅ H) (c' : H ≅ F)
    (h₁ : b ≪≫ c = t ≪≫ s) (h₂ : a ≪≫ t = a' ≪≫ b') (h₃ : s ≪≫ d = c') :
    a ≪≫ b ≪≫ c ≪≫ d ≪≫ e = a' ≪≫ b' ≪≫ c' ≪≫ e := by
  rw [← Iso.trans_assoc b c, h₁]
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc a t, h₂]
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc s d, h₃]

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.ChainComposition
