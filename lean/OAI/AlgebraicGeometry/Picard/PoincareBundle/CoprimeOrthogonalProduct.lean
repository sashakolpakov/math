import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimePairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Coprime Orthogonal Product -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct

noncomputable section

/-! Orthogonality of a product with a coprime finite group-scheme factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal

variable {S : Scheme.{u}} {H K D : Over S} [GrpObj K] [GrpObj D]

/-- The first actual product subgroup inclusion. -/
def first : K ⟶ K ⊗ D := lift (𝟙 K) 1

/-- The complementary actual product subgroup inclusion. -/
def second : D ⟶ K ⊗ D := lift 1 (𝟙 D)

instance first_isMonHom : IsMonHom (first (K := K) (D := D)) := by
  have : IsMonHom (1 : K ⟶ D) := by
    change IsMonHom (toUnit K ≫ MonObj.one)
    infer_instance
  dsimp [first]
  infer_instance

instance second_isMonHom : IsMonHom (second (K := K) (D := D)) := by
  have : IsMonHom (1 : D ⟶ K) := by
    change IsMonHom (toUnit D ≫ MonObj.one)
    infer_instance
  dsimp [second]
  infer_instance

variable (e : ∀ T : Over S, (T ⟶ K ⊗ D) →* (T ⟶ K ⊗ D) →* Γ(T.left, ⊤)ˣ)

/-- Restriction of the pairing to the first represented factor. -/
def firstPairing (T : Over S) : (T ⟶ K) →* (T ⟶ K) →* Γ(T.left, ⊤)ˣ :=
  ((MonoidHom.compHom' (P := Γ(T.left, ⊤)ˣ)
    (Kernel.Scheme.pointsMap (first (K := K) (D := D)) T)).comp
      (e T)).comp (Kernel.Scheme.pointsMap first T)

/-- Multiplying the two coordinate inclusions recovers each scheme-valued point. -/
theorem factors {T : Over S} (y : T ⟶ K ⊗ D) :
    (y ≫ fst K D ≫ first) * (y ≫ snd K D ≫ second) = y := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [first, second, MonObj.mul_comp]

variable (n m : ℕ) (hnm : n.Coprime m)
  (hK : ∀ (T : Over S) (x : T ⟶ K), x ^ n = 1)
  (hD : ∀ (T : Over S) (x : T ⟶ D), x ^ m = 1)

include hnm hK hD

/-- The two genuine represented factors pair trivially by their coprime annihilators. -/
theorem cross_eq_one {T : Over S} (x : T ⟶ K) (y : T ⟶ D) : e T (x ≫ first) (y ≫ second) = 1 := by
  apply CoprimePairing.value_eq_one (e T) n m hnm
  · rw [← MonObj.pow_comp, hK T x, MonObj.one_comp]
  · rw [← MonObj.pow_comp, hD T y, MonObj.one_comp]

/-- Pairing against the first factor depends only on the first coordinate of the second point. -/
theorem pairing_first {T : Over S} (x : T ⟶ K) (y : T ⟶ K ⊗ D) :
    e T (x ≫ first) y = firstPairing e T x (y ≫ fst K D) := by
  have hc : e T (x ≫ first) (y ≫ snd K D ≫ second) = 1 := by
    simpa only [Category.assoc] using cross_eq_one e n m hnm hK hD x (y ≫ snd K D)
  calc
    e T (x ≫ first) y = e T (x ≫ first)
        ((y ≫ fst K D ≫ first) * (y ≫ snd K D ≫ second)) :=
      congrArg (e T (x ≫ first)) (factors y).symm
    _ = e T (x ≫ first) (y ≫ fst K D ≫ first) := by rw [map_mul, hc, mul_one]
    _ = firstPairing e T x (y ≫ fst K D) := rfl

/-- The full all-base-change orthogonal is the inverse image of the first-factor orthogonal. -/
theorem orthogonal_iff (i : H ⟶ K) {T : Over S} (y : T ⟶ K ⊗ D) :
    y ∈ NaturalPairingOrthogonal.orthogonal (i ≫ first) e T ↔ (y ≫ fst K D) ∈ NaturalPairingOrthogonal.orthogonal i (firstPairing e) T := by
  constructor
  · intro h U a k
    have he := h U a k
    rw [← Category.assoc, pairing_first e n m hnm hK hD] at he
    simpa only [Category.assoc] using he
  · intro h U a k
    rw [← Category.assoc, pairing_first e n m hnm hK hD]
    simpa only [Category.assoc] using h U a k

/-- Self-annihilation in the torsion factor leaves the entire coprime factor in the full orthogonal. -/
theorem orthogonal_of_selfAnnihilating (i : H ⟶ K) (hi : NaturalPairingOrthogonal.SelfAnnihilating i (firstPairing e))
    {T : Over S} (y : T ⟶ K ⊗ D) :
    y ∈ NaturalPairingOrthogonal.orthogonal (i ≫ first) e T ↔ ∃ k : T ⟶ H, k ≫ i = y ≫ fst K D :=
  (orthogonal_iff e n m hnm hK hD i y).trans (hi T (y ≫ fst K D))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct
