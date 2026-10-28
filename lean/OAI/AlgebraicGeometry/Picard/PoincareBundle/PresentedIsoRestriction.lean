import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.SymmetryFibers

/-! # Presented Iso Restriction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedIsoRestriction

noncomputable section

/-! Restricting an actual isomorphism through its source and target presentations. -/

open _root_.CategoryTheory

/-- Three commuting actual comparison squares give the exact restriction of the presented map. -/
theorem restrict {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B M N : C} {A' B' M' N' : D}
    (s : A ≅ M) (t : B ≅ N) (e : A ≅ B)
    (s' : A' ≅ M') (t' : B' ≅ N') (e' : A' ≅ B')
    (a : F.obj A ≅ A') (b : F.obj B ≅ B') (m : F.obj M ≅ M') (n : F.obj N ≅ N')
    (hs : F.mapIso s ≪≫ m = a ≪≫ s') (ht : F.mapIso t ≪≫ n = b ≪≫ t')
    (he : F.mapIso e ≪≫ b = a ≪≫ e') :
    m.symm ≪≫ F.mapIso (s.symm ≪≫ e ≪≫ t) ≪≫ n = s'.symm ≪≫ e' ≪≫ t' := by
  have hEt : F.mapIso (e ≪≫ t) ≪≫ n = a ≪≫ e' ≪≫ t' := by
    rw [Functor.mapIso_trans, Iso.trans_assoc, ht, ← Iso.trans_assoc, he, Iso.trans_assoc]
  have h := Line.SymmetryFibers.inverse_functor_square F s (e ≪≫ t) s' (e' ≪≫ t') a m n hs hEt
  have hh := congrArg (fun v => m.symm ≪≫ v) h
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc] using hh

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedIsoRestriction
