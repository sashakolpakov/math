import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CochainTruncation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.DualFunctor
import Mathlib.Algebra.Homology.Embedding.Restriction

/-! # Dual Cochain -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.DualCochain

noncomputable section

/-! The reversed dual of a finite cochain interval is again a nonnegative cochain complex, concentrated in the same interval. Its terms are the actual module duals, with finite freeness preserved. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u

def finiteDualEmbedding (g : ℕ) : ComplexShape.Embedding (HilbertConstruction.Finite.CochainTruncation.finiteCochainShape g) (.down ℕ) :=
  ComplexShape.Embedding.mk' _ _ (fun i => i.rev.val)
    (fun i j h => by
      have he : i.rev = j.rev := Fin.ext h
      simpa only [Fin.rev_rev] using congrArg Fin.rev he)
    (fun i j => by
      change i.val + 1 = j.val ↔ j.rev.val + 1 = i.rev.val
      rw [Fin.val_rev, Fin.val_rev]
      have hi := i.isLt
      have hj := j.isLt
      omega)

instance finiteDualEmbedding_isRelIff (g : ℕ) : (finiteDualEmbedding g).IsRelIff where
  rel' i j h := by
    change j.rev.val + 1 = i.rev.val at h
    change i.val + 1 = j.val
    simp only [Fin.val_rev] at h
    have := i.isLt
    have := j.isLt
    omega

instance finiteDualEmbedding_isTruncGE (g : ℕ) : (finiteDualEmbedding g).IsTruncGE where
  toIsRelIff := inferInstance
  mem_next {j k} h := by
    change k + 1 = j.rev.val at h
    have hk : k < g + 1 := by have := j.rev.isLt; omega
    refine ⟨(⟨k, hk⟩ : Fin (g + 1)).rev, ?_⟩
    change ((⟨k, hk⟩ : Fin (g + 1)).rev.rev).val = k
    rw [Fin.rev_rev]

theorem finiteDualEmbedding_outside_iff (g q : ℕ) :
    (∀ i, (finiteDualEmbedding g).f i ≠ q) ↔ g < q := by
  constructor
  · intro h
    by_contra hn
    have hq : q < g + 1 := Nat.lt_succ_of_le (Nat.le_of_not_gt hn)
    apply h (⟨q, hq⟩ : Fin (g + 1)).rev
    change ((⟨q, hq⟩ : Fin (g + 1)).rev.rev).val = q
    rw [Fin.rev_rev]
  · intro h i hi
    change i.rev.val = q at hi
    have := i.rev.isLt
    omega

variable {R : Type u} [CommRing R]

def finiteDualCochain (C : CochainComplex (ModuleCat.{u} R) ℕ) (g : ℕ) :
    HomologicalComplex (ModuleCat.{u} R) (HilbertConstruction.Finite.CochainTruncation.finiteCochainShape g) :=
  let D : ChainComplex (ModuleCat.{u} R) ℕ := HilbertConstruction.Module.DualFunctor.dualModuleComplex C
  D.restriction (finiteDualEmbedding g)

def boundedDualCochain (C : CochainComplex (ModuleCat.{u} R) ℕ) (g : ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (finiteDualCochain C g).extend (HilbertConstruction.Finite.CochainTruncation.finiteCochainEmbedding g)

def boundedDualCochainXIso (C : CochainComplex (ModuleCat.{u} R) ℕ) (g q : ℕ) (hq : q ≤ g) :
    (boundedDualCochain C g).X q ≅ ModuleCat.of R (Module.Dual R (C.X (g - q))) := by
  let i : Fin (g + 1) := ⟨q, Nat.lt_succ_of_le hq⟩
  let e := (finiteDualCochain C g).extendXIso (HilbertConstruction.Finite.CochainTruncation.finiteCochainEmbedding g) (i := i) (i' := q) rfl
  change (boundedDualCochain C g).X q ≅ ModuleCat.of R (Module.Dual R (C.X i.rev.val)) at e
  have hi : i.rev.val = g - q := by
    simp only [Fin.val_rev, i, Nat.add_sub_add_right]
  rw [hi] at e
  exact e

theorem boundedDualCochain_isZero_above
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (g q : ℕ) (hq : g < q) :
    IsZero ((boundedDualCochain C g).X q) :=
  (finiteDualCochain C g).isZero_extend_X (HilbertConstruction.Finite.CochainTruncation.finiteCochainEmbedding g) q
    ((HilbertConstruction.Finite.CochainTruncation.finiteCochainEmbedding_outside_iff g q).mpr hq)

theorem boundedDualCochain_finite_free
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (g : ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q)) :
    ∀ q, Module.Finite R ((boundedDualCochain C g).X q) ∧
      Module.Free R ((boundedDualCochain C g).X q) := by
  intro q
  by_cases hq : q ≤ g
  · have : Module.Finite R (C.X (g - q)) := hfin (g - q)
    have : Module.Free R (C.X (g - q)) := hfree (g - q)
    let e := (boundedDualCochainXIso C g q hq).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
  · have : Subsingleton ((boundedDualCochain C g).X q) :=
      ModuleCat.subsingleton_of_isZero (boundedDualCochain_isZero_above C g q (Nat.lt_of_not_ge hq))
    exact ⟨inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.DualCochain
