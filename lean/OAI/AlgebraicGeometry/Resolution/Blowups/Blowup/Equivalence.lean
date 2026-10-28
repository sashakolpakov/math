import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Functor

/-! # Equivalence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Equivalence.Construction

noncomputable section

/-! Affine Rees blowups respect actual equivalences of coefficient rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineBlowupMapTo_isIso_of_equiv
    {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S) (h : I.map e.toRingHom = J) :
    IsIso (Functor.Construction.affineBlowupMapTo I J e.toRingHom h) := by
  have hi : J.map e.symm.toRingHom = I := by
    rw [← h, Ideal.map_map]
    simp
  have h₁ : e.toRingHom.comp e.symm.toRingHom = RingHom.id S := by ext; simp
  have h₂ : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by ext; simp
  refine ⟨⟨Functor.Construction.affineBlowupMapTo J I e.symm.toRingHom hi, ?_, ?_⟩⟩
  · rw [← Functor.Construction.affineBlowupMapTo_comp J I J e.symm.toRingHom e.toRingHom hi h
      (by rw [h₁]; exact Ideal.map_id J)]
    simp only [h₁, Functor.Construction.affineBlowupMapTo_id]
  · rw [← Functor.Construction.affineBlowupMapTo_comp I J I e.toRingHom e.symm.toRingHom h hi
      (by rw [h₂]; exact Ideal.map_id I)]
    simp only [h₂, Functor.Construction.affineBlowupMapTo_id]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Equivalence.Construction
