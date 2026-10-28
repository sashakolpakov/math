import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SheafComplexGlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SupportedComplexRestriction

/-! # Acyclic Sheaf Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.AcyclicSheafSections

noncomputable section

/-! Shift a complex bounded below into nonnegative degrees to recover
surjectivity on global sections at its zero upper endpoint. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u

def shiftedNonnegativeCochainEmbedding (a : ℤ) : ComplexShape.Embedding (.up ℕ) (.up ℤ) :=
  ComplexShape.Embedding.mk' _ _ (fun n => (n : ℤ) + a)
    (fun i j h => by
      change (i : ℤ) + a = (j : ℤ) + a at h
      omega)
    (fun i j => by change i + 1 = j ↔ (i : ℤ) + a + 1 = (j : ℤ) + a; omega)

instance shiftedNonnegativeCochainEmbedding_isRelIff (a : ℤ) :
    (shiftedNonnegativeCochainEmbedding a).IsRelIff where
  rel' := by
    intro i j h
    change (i : ℤ) + a + 1 = (j : ℤ) + a at h
    change i + 1 = j
    omega

theorem shiftedNonnegativeCochainEmbedding_outside_iff (a i : ℤ) :
    (∀ n, (shiftedNonnegativeCochainEmbedding a).f n ≠ i) ↔ i < a := by
  constructor
  · intro h
    by_contra hn
    apply h (i - a).toNat
    change ((i - a).toNat : ℤ) + a = i
    omega
  · intro hi n hn
    change (n : ℤ) + a = i at hn
    omega

namespace NativeCech
variable {X : TopCat.{u}}

theorem bounded_acyclic_sheafComplex_last_sections_surjective
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ) (hK : K.Acyclic)
    (hH : ∀ i q, Subsingleton (CategoryTheory.Sheaf.H (K.X i) (q + 1)))
    (r : ℕ) (hbelow : ∀ i : ℤ, i < -(r : ℤ) → IsZero (K.X i))
    (habove : IsZero (K.X 1)) :
    Function.Surjective ((K.d (-1) 0).hom.app (op (⊤ : Opens X))) := by
  let a : ℤ := -((r + 1 : ℕ) : ℤ)
  let e := shiftedNonnegativeCochainEmbedding a
  let : K.IsStrictlySupported e := {
    isZero := fun i hi => hbelow i (by
      have := (shiftedNonnegativeCochainEmbedding_outside_iff a i).mp hi
      dsimp [a] at this
      omega) }
  let C := K.restriction e
  have hC : C.Acyclic := SupportedComplexRestriction.strictlySupported_restriction_acyclic e K hK
  have hn : (r : ℤ) + a = -1 := by dsimp [a]; omega
  have hn1 : ((r + 1 : ℕ) : ℤ) + a = 0 := by dsimp [a]; omega
  have hn2 : ((r + 2 : ℕ) : ℤ) + a = 1 := by dsimp [a]; omega
  have hnext : IsZero (C.X (r + 2)) := by
    change IsZero (K.X (((r + 2 : ℕ) : ℤ) + a))
    rw [hn2]
    exact habove
  have hs := SheafComplexGlobalSections.IntrinsicCech.acyclic_sheafComplex_last_sections_surjective C hC
    (fun i q => hH ((i : ℤ) + a) q) r hnext
  change Function.Surjective
    ((K.d ((r : ℤ) + a) (((r + 1 : ℕ) : ℤ) + a)).hom.app (op (⊤ : Opens X))) at hs
  rw [hn, hn1] at hs
  exact hs

end NativeCech

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.AcyclicSheafSections
