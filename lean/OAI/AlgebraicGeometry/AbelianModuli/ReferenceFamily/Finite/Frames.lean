import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Cover
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Tactic

/-! # Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.Frames.LevelCover

noncomputable section

/-! The nonvanishing relation equations used by the frame scheme are
exactly the injectivity condition for a basis of the finite torsion group. -/

open scoped BigOperators

variable {G : Type*} [CommGroup G] {N r : ℕ}

def coefficientHom (a : G) (ha : a ^ N = 1) : ZMod N →+ Additive G :=
  ZMod.lift N ⟨zmultiplesHom (Additive G) (Additive.ofMul a), by
    change Additive.ofMul (a ^ (N : ℤ)) = 0
    simpa using congrArg Additive.ofMul ha⟩

theorem coefficientHom_val [NeZero N] (a : G) (ha : a ^ N = 1) (c : ZMod N) :
    coefficientHom a ha c = Additive.ofMul (a ^ c.val) := by
  have hc : ((c.val : ℤ) : ZMod N) = c := by simp
  calc
    coefficientHom a ha c = coefficientHom a ha ((c.val : ℤ) : ZMod N) :=
      congrArg (coefficientHom a ha) hc.symm
    _ = (zmultiplesHom (Additive G) (Additive.ofMul a)) (c.val : ℤ) :=
      ZMod.lift_coe N _ _
    _ = Additive.ofMul (a ^ c.val) := by
      change Additive.ofMul (a ^ (c.val : ℤ)) = _
      simp only [zpow_natCast]

def frameHom (a : Fin r → G) (ha : ∀ i, a i ^ N = 1) :
    Multiplicative (Fin r → ZMod N) →* G :=
  AddMonoidHom.toMultiplicativeLeft
    (∑ i : Fin r, (coefficientHom (a i) (ha i)).comp
      (Pi.evalAddMonoidHom (fun _ : Fin r => ZMod N) i))

theorem frameHom_apply [NeZero N] (a : Fin r → G) (ha : ∀ i, a i ^ N = 1)
    (c : Fin r → ZMod N) :
    frameHom a ha (Multiplicative.ofAdd c) = ∏ i, a i ^ (c i).val := by
  simp [frameHom, AddMonoidHom.toMultiplicativeLeft, coefficientHom_val]

/-- The frame equations assert precisely that this homomorphism has
trivial kernel, hence is injective. -/
theorem frameHom_injective [NeZero N] (a : Fin r → G) (ha : ∀ i, a i ^ N = 1)
    (hind : ∀ c : Fin r → ZMod N, c ≠ 0 → (∏ i, a i ^ (c i).val) ≠ 1) :
    Function.Injective (frameHom a ha) := by
  apply (MonoidHom.ker_eq_bot_iff (frameHom a ha)).mp
  apply le_antisymm ?_ bot_le
  intro c hc
  change frameHom a ha c = 1 at hc
  change c = 1
  apply Multiplicative.toAdd.injective
  by_contra hne
  exact hind c.toAdd hne ((frameHom_apply a ha c.toAdd).symm.trans hc)

/-- Equal finite cardinality turns the explicitly constructed independent
frame into the full level isomorphism on the torsion group. -/
def fullFrame [NeZero N] [Fintype G]
    (a : Fin r → G) (ha : ∀ i, a i ^ N = 1)
    (hind : ∀ c : Fin r → ZMod N, c ≠ 0 → (∏ i, a i ^ (c i).val) ≠ 1)
    (hcard : Fintype.card G = N ^ r) :
    Multiplicative (Fin r → ZMod N) ≃* G :=
  MulEquiv.ofBijective (frameHom a ha) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨frameHom_injective a ha hind, ?_⟩
    simpa using hcard.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.Frames.LevelCover
