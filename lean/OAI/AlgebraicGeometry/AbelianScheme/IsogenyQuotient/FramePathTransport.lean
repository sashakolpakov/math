import Mathlib.CategoryTheory.Iso

/-! # Frame Path Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramePathTransport.Construction

/-! Substitute a recovered frame in a finite path of actual line
isomorphisms, retaining all endpoint comparisons. -/

open _root_.CategoryTheory

theorem frame_three_steps {C : Type*} [Category* C] {O A B D E : C}
    (s : O ≅ A) (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (t : O ≅ B) (h : s ≪≫ a = t) :
    s ≪≫ (a ≪≫ b ≪≫ c) = (t ≪≫ b) ≪≫ c := by
  rw [← h]
  simp only [Iso.trans_assoc]

theorem frame_four_steps {C : Type*} [Category* C] {O A B D E F G : C}
    (s : O ≅ A) (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (d : E ≅ F) (e : F ≅ G)
    (t : O ≅ B) (h : s ≪≫ a = t) :
    (s ≪≫ (a ≪≫ b ≪≫ c ≪≫ d)) ≪≫ e = (t ≪≫ b) ≪≫ (c ≪≫ d ≪≫ e) := by
  rw [← h]
  simp only [Iso.trans_assoc]

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramePathTransport.Construction
