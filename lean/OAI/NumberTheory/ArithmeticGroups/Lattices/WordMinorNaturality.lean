import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.WordMinors
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Word Minor Naturality -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.WordMinorNaturality.Construction

noncomputable section

/-! Word actions and their minors commute with scalar maps and intertwining maps. -/

open scoped Classical

theorem matrixWordAction_intertwines
    {R S ι : Type*} [CommRing R] [CommRing S] {n m : ℕ}
    (A : ι → Matrix (Fin n) (Fin n) R) (B : ι → Matrix (Fin m) (Fin m) S)
    (f : (Fin n → R) → (Fin m → S))
    (h : ∀ i x, f ((A i).mulVec x) = (B i).mulVec (f x)) (w : List ι) (x : Fin n → R) :
    f (Finite.WordMinors.Construction.matrixWordAction A w x) = Finite.WordMinors.Construction.matrixWordAction B w (f x) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [Finite.WordMinors.Construction.matrixWordAction, h, ih]

theorem matrixWordAction_map
    {R S ι : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (σ : R →+* S) (A : ι → Matrix (Fin n) (Fin n) R) (w : List ι) (x : Fin n → R) :
    (fun i => σ (Finite.WordMinors.Construction.matrixWordAction A w x i)) =
      Finite.WordMinors.Construction.matrixWordAction (fun i => (A i).map σ) w (fun i => σ (x i)) := by
  apply matrixWordAction_intertwines A (fun i => (A i).map σ) (fun x i => σ (x i)) _ w x
  intro i y
  funext j
  exact RingHom.map_mulVec σ (A i) y j

theorem boundedWordMinor_map
    {R S ι : Type*} [CommRing R] [CommRing S] {n d : ℕ}
    (σ : R →+* S) (q : Finite.WordMinors.Construction.boundedWordMinorIndex ι n d)
    (A : ι → Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    σ (Finite.WordMinors.Construction.boundedWordMinor q A x) =
      Finite.WordMinors.Construction.boundedWordMinor q (fun i => (A i).map σ) (fun i => σ (x i)) := by
  rw [Finite.WordMinors.Construction.boundedWordMinor, RingHom.map_det, Finite.WordMinors.Construction.boundedWordMinor]
  congr 1
  ext i j : 1
  exact congrFun (matrixWordAction_map σ A ((q.2.1 j).toList) x) (q.2.2 i)

theorem matrixWordAction_conjugate
    {R ι : Type*} [CommRing R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R)
    (A : ι → Matrix (Fin n) (Fin n) R) (w : List ι) (x : Fin n → R) :
    g.val.mulVec (Finite.WordMinors.Construction.matrixWordAction A w x) =
      Finite.WordMinors.Construction.matrixWordAction (fun i => g.val * A i * (g⁻¹).val) w (g.val.mulVec x) := by
  apply matrixWordAction_intertwines A _ g.val.mulVec _ w x
  intro i y
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul,
    mul_one]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.WordMinorNaturality.Construction
