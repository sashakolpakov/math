import Mathlib.Algebra.Homology.Homotopy

/-! # Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Composition.Comparison

noncomputable section

/-! An incoming comparison homotopy can be precomposed with a local
frame comparison and transported across a reindexed section family. -/

open _root_.CategoryTheory

theorem factorization {C : Type*} [Category C] {X K L A B : C}
    (eK : K ≅ A) (eL : L ≅ B) (b : A ⟶ B) (a : X ⟶ K) (q : X ⟶ L)
    (h : q ≫ eL.hom = (a ≫ eK.hom) ≫ b) :
    q = a ≫ (eK.hom ≫ b ≫ eL.inv) := by
  apply (cancel_mono eL.hom).1
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {C : Type*} [Category C] [Preadditive C]
  {K A B I K' B' I' : CochainComplex C ℕ}

private theorem endpoint (p : K ⟶ A) (f : A ⟶ B) (b : B ⟶ I)
    (sB : B ⟶ B') (sI : I ⟶ I') (b' : B' ⟶ I')
    (sK : K ⟶ K') (p' : K' ⟶ B')
    (hb : b ≫ sI = sB ≫ b') (hp : (p ≫ f) ≫ sB = sK ≫ p') :
    (p ≫ (f ≫ b)) ≫ sI = (sK ≫ p') ≫ b' := by
  calc
    (p ≫ (f ≫ b)) ≫ sI = (p ≫ f) ≫ (b ≫ sI) := by simp only [Category.assoc]
    _ = ((p ≫ f) ≫ sB) ≫ b' := by rw [hb]; simp only [Category.assoc]
    _ = (sK ≫ p') ≫ b' := congrArg (fun a => a ≫ b') hp

def homotopy (p : K ⟶ A) (f : A ⟶ B) (a : A ⟶ I) (b : B ⟶ I)
    (h : Homotopy a (f ≫ b))
    (sB : B ⟶ B') (sI : I ⟶ I') (b' : B' ⟶ I')
    (sK : K ⟶ K') (p' : K' ⟶ B')
    (hb : b ≫ sI = sB ≫ b') (hp : (p ≫ f) ≫ sB = sK ≫ p') :
    Homotopy ((p ≫ a) ≫ sI) ((sK ≫ p') ≫ b') :=
  ((h.compLeft p).compRight sI).trans
    (Homotopy.ofEq (endpoint p f b sB sI b' sK p' hb hp))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Composition.Comparison
