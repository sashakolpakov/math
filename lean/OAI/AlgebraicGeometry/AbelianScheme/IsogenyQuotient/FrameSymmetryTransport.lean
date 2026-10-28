import Mathlib.CategoryTheory.Iso

/-! # Frame Symmetry Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FrameSymmetryTransport.Construction

/-! A frame recovered through a fiber comparison gives the same
transported symmetric frame after all comparisons are composed. -/

open _root_.CategoryTheory

theorem frame_symmetry_transport {C : Type*} [Category* C] {O X Y Z V W : C}
    (s : O ≅ X) (a : X ≅ Y) (b : Z ≅ X) (e : Z ≅ V) (c : V ≅ W) (t : O ≅ Y)
    (h : s ≪≫ a = t) :
    ((s ≪≫ b.symm) ≪≫ e) ≪≫ c = t ≪≫ (a.symm ≪≫ b.symm ≪≫ e ≪≫ c) := by
  rw [← h]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FrameSymmetryTransport.Construction
