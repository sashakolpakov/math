import Mathlib.Algebra.Homology.Embedding.TruncLEHomology

/-! # Cochain Truncation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CochainTruncation

noncomputable section

/-! Canonical upper truncation for nonnegative cochain complexes, using the finite shape with vertices 0 through g and the actual cycle object at its final vertex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v

def finiteCochainShape (g : ℕ) : ComplexShape (Fin (g + 1)) where
  Rel i j := i.val + 1 = j.val
  next_eq h h' := Fin.ext (h.symm.trans h')
  prev_eq h h' := Fin.ext (Nat.add_right_cancel (h.trans h'.symm))

def finiteCochainEmbedding (g : ℕ) :
    ComplexShape.Embedding (finiteCochainShape g) (.up ℕ) :=
  ComplexShape.Embedding.mk' _ _ Fin.val Fin.val_injective (fun _ _ => Iff.rfl)

instance finiteCochainEmbedding_isRelIff (g : ℕ) : (finiteCochainEmbedding g).IsRelIff where
  rel' _ _ h := h

instance finiteCochainEmbedding_isTruncLE (g : ℕ) : (finiteCochainEmbedding g).IsTruncLE where
  toIsRelIff := inferInstance
  mem_prev {i j} h := by
    change i + 1 = j.val at h
    refine ⟨⟨i, ?_⟩, rfl⟩
    have hj := j.isLt
    omega

theorem finiteCochainEmbedding_boundary_iff (g : ℕ) (i : Fin (g + 1)) :
    (finiteCochainEmbedding g).BoundaryLE i ↔ i.val = g := by
  constructor
  · intro h
    by_contra hi
    have hlt : i.val < g := by have := i.isLt; omega
    let j : Fin (g + 1) := ⟨i.val + 1, Nat.add_lt_add_right hlt 1⟩
    exact h.2 j rfl
  · intro hi
    apply (finiteCochainEmbedding g).boundaryLE (k' := g + 1)
    · change i.val + 1 = g + 1
      rw [hi]
    · intro j hj
      change j.val = g + 1 at hj
      exact (Nat.ne_of_lt j.isLt) hj

theorem finiteCochainEmbedding_outside_iff (g q : ℕ) :
    (∀ i, (finiteCochainEmbedding g).f i ≠ q) ↔ g < q := by
  constructor
  · intro h
    by_contra hn
    have hq : q < g + 1 := Nat.lt_succ_of_le (Nat.le_of_not_gt hn)
    exact h ⟨q, hq⟩ rfl
  · intro h i hi
    change i.val = q at hi
    have := i.isLt
    omega

variable {C : Type u} [Category.{v} C] [Abelian C]

def finiteCochainTruncation (K : CochainComplex C ℕ) (g : ℕ) : CochainComplex C ℕ :=
  K.truncLE (finiteCochainEmbedding g)

def finiteCochainTruncationι (K : CochainComplex C ℕ) (g : ℕ) :
    finiteCochainTruncation K g ⟶ K := K.ιTruncLE (finiteCochainEmbedding g)

def finiteCochainTruncationXIso (K : CochainComplex C ℕ) (g q : ℕ) (hq : q < g) :
    (finiteCochainTruncation K g).X q ≅ K.X q :=
  K.truncLEXIso (finiteCochainEmbedding g) (i := ⟨q, Nat.lt_trans hq (Nat.lt_succ_self g)⟩) rfl
    (fun h => (Nat.ne_of_lt hq) ((finiteCochainEmbedding_boundary_iff g _).mp h))

def finiteCochainTruncationLastIso (K : CochainComplex C ℕ) (g : ℕ) :
    (finiteCochainTruncation K g).X g ≅ K.cycles g :=
  K.truncLEXIsoCycles (finiteCochainEmbedding g) (i := ⟨g, Nat.lt_succ_self g⟩) rfl
    ((finiteCochainEmbedding_boundary_iff g _).mpr rfl)

theorem finiteCochainTruncation_isZero_above (K : CochainComplex C ℕ) (g q : ℕ) (hq : g < q) :
    IsZero ((finiteCochainTruncation K g).X q) :=
  (K.truncLE (finiteCochainEmbedding g)).isZero_X_of_isStrictlySupported
    (finiteCochainEmbedding g) q ((finiteCochainEmbedding_outside_iff g q).mpr hq)

theorem finiteCochainTruncation_quasiIso (K : CochainComplex C ℕ) (g : ℕ)
    (hK : ∀ q, g < q → K.ExactAt q) : QuasiIso (finiteCochainTruncationι K g) := by
  apply (K.quasiIso_ιTruncLE_iff_isSupported (finiteCochainEmbedding g)).mpr
  exact ⟨fun q hq => hK q ((finiteCochainEmbedding_outside_iff g q).mp hq)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CochainTruncation
