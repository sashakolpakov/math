import Mathlib.CategoryTheory.Iso

/-! # Iso Transport Conjugation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoTransportConjugation

/-! Cancellation of coordinate changes around a transported isomorphism. -/

open _root_.CategoryTheory

universe u₁ u₂ v₁ v₂

theorem isoTransportConjugation
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : C ⥤ D) {FL FR JL JR : C} {NL NR A B L R : D}
    (qL : FL ≅ JL) (qR : FR ≅ JR) (e : FL ≅ FR)
    (nL : NL ≅ K.obj FL) (nR : NR ≅ K.obj FR)
    (ea : A ≅ NL) (eb : B ≅ NR) (zL : K.obj JL ≅ L) (zR : K.obj JR ≅ R)
    (Aiso : A ≅ L) (Biso : B ≅ R) (Tiso : L ≅ R)
    (hA : Aiso = ea ≪≫ nL ≪≫ K.mapIso qL ≪≫ zL)
    (hB : Biso = eb ≪≫ nR ≪≫ K.mapIso qR ≪≫ zR)
    (hT : Tiso = zL.symm ≪≫ K.mapIso (qL.symm ≪≫ e ≪≫ qR) ≪≫ zR) :
    Aiso ≪≫ Tiso ≪≫ Biso.symm =
      ea ≪≫ (nL ≪≫ K.mapIso e ≪≫ nR.symm) ≪≫ eb.symm := by
  rw [hA, hT, hB]
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_symm, Iso.trans_assoc,
    Iso.self_symm_id_assoc]

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoTransportConjugation
