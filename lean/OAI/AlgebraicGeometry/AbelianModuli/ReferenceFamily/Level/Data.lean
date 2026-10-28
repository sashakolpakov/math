import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-! # Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Data

noncomputable section

/-! The auxiliary coprime level and the prescribed full level are distinct.
These constructions use HilbertConstruction's actual group-scheme functors of points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- A fine auxiliary level can be chosen prime to both the polarization
product and the independently prescribed level. -/
theorem exists_auxiliary_level (D N : ℕ) (hD : 0 < D) (hN : 0 < N) :
    ∃ L : ℕ, 3 ≤ L ∧ Nat.Coprime L D ∧ Nat.Coprime L N := by
  let L := 2 * (D * N) + 1
  have hpos : 0 < D * N := Nat.mul_pos hD hN
  have hcoprime : Nat.Coprime L (D * N) := by
    dsimp only [L]
    rw [Nat.coprime_mul_right_add_left]
    simp
  exact ⟨L, by dsimp [L]; omega,
    hcoprime.coprime_dvd_right (dvd_mul_right D N),
    hcoprime.coprime_dvd_right (dvd_mul_left N D)⟩

/-- Both markings belong to the same polarized abelian scheme. No
coprimality condition is imposed on the prescribed level N. -/
structure AddedFullLevel (g : ℕ) (δ : Fin g → ℕ) (L N : ℕ)
    (S : Scheme.{u}) where
  auxiliary : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ L S
  prescribed : auxiliary.abelian.FullLevel N

namespace AddedFullLevel

variable {g L N : ℕ} {δ : Fin g → ℕ} {S : Scheme.{u}}

/-- Forget the auxiliary marking and retain exactly the requested N-level. -/
def forgetAuxiliary (A : AddedFullLevel g δ L N S) :
    HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S where
  abelian := A.auxiliary.abelian
  dual := A.auxiliary.dual
  polarization := A.auxiliary.polarization
  level := A.prescribed

/-- Interchange the two markings without altering the polarized abelian data. -/
def swap (A : AddedFullLevel g δ L N S) : AddedFullLevel g δ N L S where
  auxiliary := A.forgetAuxiliary
  prescribed := A.auxiliary.level

@[simp] theorem swap_swap (A : AddedFullLevel g δ L N S) : A.swap.swap = A := by
  cases A
  rfl

end AddedFullLevel

section Frames

variable {C : Type*} [Category C] {X Y : C}

/-- Once one frame is chosen, all frames are obtained by a unique change
of basis. This applies to HilbertConstruction's full-level isomorphisms of group functors. -/
def framesEquivAut (frame : X ≅ Y) : (X ≅ Y) ≃ (X ≅ X) where
  toFun other := other ≪≫ frame.symm
  invFun change := change ≪≫ frame
  left_inv other := by ext; simp
  right_inv change := by ext; simp

theorem existsUnique_change_of_frame (frame other : X ≅ Y) :
    ∃! change : X ≅ X, change ≪≫ frame = other := by
  refine ⟨framesEquivAut frame other, (framesEquivAut frame).symm_apply_apply other, ?_⟩
  intro change h
  apply (framesEquivAut frame).symm.injective
  exact h.trans ((framesEquivAut frame).symm_apply_apply other).symm

end Frames

/-- The fibers of forgetting an auxiliary full level are its actual
functor-of-points frames, with the explicit change-of-basis description. -/
def auxiliaryFramesEquiv
    {g L : ℕ} {S : Scheme.{u}} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (frame : A.FullLevel L) :
    A.FullLevel L ≃
      (HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g L S ≅
        HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g L S) :=
  framesEquivAut frame

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Data
