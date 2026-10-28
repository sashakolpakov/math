import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberPointEquality

/-! # Fiber Point Transport Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberPointTransportNaturality.Construction

noncomputable section

/-! Equality transports between actual point fibers commute with
every change of test scheme and its canonical pullback comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

universe u

theorem fiberPointIso_pullback {S : Scheme.{u}} {E T T' : Over S}
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (f : T' ⟶ T)
    (x y : T ⟶ E) (h : x = y) (x' y' : T' ⟶ E) (h' : x' = y')
    (hx : f ≫ x = x') (hy : f ≫ y = y') :
    (Scheme.Modules.pullback f.left).mapIso (FiberPointEquality.Construction.fiberPointIso L x y h) ≪≫ Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L f y y' hy =
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L f x x' hx ≪≫ FiberPointEquality.Construction.fiberPointIso L x' y' h' := by
  cases h
  cases h'
  simp only [FiberPointEquality.Construction.fiberPointIso_refl, Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl]

theorem iso_square_comp {C : Type*} [Category* C] {A B C' A' B' C'' : C}
    (e : A ≅ B) (d : B ≅ C') (e' : A' ≅ B') (d' : B' ≅ C'')
    (a : A ≅ A') (b : B ≅ B') (c : C' ≅ C'')
    (he : e ≪≫ b = a ≪≫ e') (hd : d ≪≫ c = b ≪≫ d') :
    (e ≪≫ d) ≪≫ c = a ≪≫ (e' ≪≫ d') := by
  rw [Iso.trans_assoc, hd, ← Iso.trans_assoc, he, Iso.trans_assoc]

theorem iso_functor_square_comp {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B C' : C} {A' B' C'' : D}
    (e : A ≅ B) (d : B ≅ C') (e' : A' ≅ B') (d' : B' ≅ C'')
    (a : F.obj A ≅ A') (b : F.obj B ≅ B') (c : F.obj C' ≅ C'')
    (he : F.mapIso e ≪≫ b = a ≪≫ e') (hd : F.mapIso d ≪≫ c = b ≪≫ d') :
    F.mapIso (e ≪≫ d) ≪≫ c = a ≪≫ (e' ≪≫ d') := by
  rw [Functor.mapIso_trans]
  exact iso_square_comp _ _ _ _ _ _ _ he hd

theorem iso_transport_eq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B : C} {A' B' : D} (e d : A ≅ B) (e' d' : A' ≅ B')
    (a : F.obj A ≅ A') (b : F.obj B ≅ B')
    (he : F.mapIso e ≪≫ b = a ≪≫ e') (hd : F.mapIso d ≪≫ b = a ≪≫ d') (h : e = d) : e' = d' := by
  cases h
  apply Iso.ext
  apply (cancel_epi a.hom).mp
  exact congrArg Iso.hom (he.symm.trans hd)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberPointTransportNaturality.Construction
