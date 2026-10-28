import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateFrame
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Adapted Etale Frame -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedEtaleFrame.Construction

noncomputable section

section

/-! Étale neighborhoods preserving a finite family of prescribed coordinates. -/

open _root_.MvPolynomial

variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]
  [Fintype ι] [DecidableEq ι]

/-- All functions in a finite dual coordinate frame can simultaneously
be retained as distinguished polynomial coordinates in an actual étale
localization around any given prime. -/
theorem exists_adapted_etale_frame (D : ι → Derivation k A A) (z : ι → A)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0) (q : Ideal A) [q.IsPrime] :
    ∃ f ∉ q, ∃ (n : ℕ) (φ : MvPolynomial (Fin n ⊕ ι) k →+* Localization.Away f),
      φ.Etale ∧ (∀ r : k, φ (C r) = algebraMap k (Localization.Away f) r) ∧
      ∀ j : ι, φ (X (Sum.inr j)) = algebraMap A (Localization.Away f) (z j) := by
  let P := MvPolynomial ι k
  let : Algebra P A := (aeval z).toRingHom.toAlgebra
  let : IsScalarTower k P A := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change algebraMap k A r = aeval z (C r)
    simp
  have hX : ∀ j, algebraMap P A (X j) = z j := by
    intro j
    change aeval z (X j) = z j
    rw [aeval_X]
  let : Algebra.Smooth P A := Blowups.Smooth.CoordinateFrame.Construction.smooth_over_coordinate_frame D (by
    intro i j
    rw [hX]
    exact hD i j)
  obtain ⟨f, hf, n, a, ht, he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := P) (S := A) (p := q)
  let B := MvPolynomial (Fin n) P
  let L := Localization.Away f
  let : Algebra B L := a
  let : SMul B L := a.toSMul
  let : IsScalarTower P B L := ht
  let : Algebra.IsStandardEtale B L := he
  let ψ : B →+* L := @algebraMap B L inferInstance inferInstance a
  let e := sumRingEquiv k (Fin n) ι
  let φ := ψ.comp e.toRingHom
  refine ⟨f, hf, n, φ, ?_, ?_, ?_⟩
  · let U := MvPolynomial (Fin n ⊕ ι) k
    let : Algebra U B := e.toRingHom.toAlgebra
    let : Algebra U L := φ.toAlgebra
    let : IsScalarTower U B L := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.Etale U B := RingHom.Etale.of_bijective (f := e.toRingHom) e.bijective
    exact Algebra.Etale.comp U B L
  · intro r
    change ψ (e (C r)) = algebraMap k L r
    rw [sumRingEquiv_C]
    calc
      ψ (C (C r)) = algebraMap P L (C r) :=
        (IsScalarTower.algebraMap_apply P B L (C r)).symm
      _ = algebraMap A L (algebraMap P A (C r)) := IsScalarTower.algebraMap_apply P A L (C r)
      _ = algebraMap A L (algebraMap k A r) := by
        congr 1
        exact (IsScalarTower.algebraMap_apply k P A r).symm
      _ = _ := (IsScalarTower.algebraMap_apply k A L r).symm
  · intro j
    change ψ (e (X (Sum.inr j))) = algebraMap A L (z j)
    rw [sumRingEquiv_X_inr]
    calc
      ψ (C (X j)) = algebraMap P L (X j) :=
        (IsScalarTower.algebraMap_apply P B L (X j)).symm
      _ = algebraMap A L (algebraMap P A (X j)) := IsScalarTower.algebraMap_apply P A L (X j)
      _ = _ := by rw [hX]

end

/-! Add a transverse hypersurface to a coordinate frame while preserving existing boundary equations. -/

variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]

def transverseExtendedCoordinates (w : ι → A) (z : A) : Option ι → A
  | none => z
  | some i => w i

/-- Correct each old derivative by its hypersurface component, retaining
its values on all boundary coordinates. -/
def transverseExtendedDerivations (D : ι → Derivation k A A) (E : Derivation k A A) (z : A) :
    Option ι → Derivation k A A
  | none => E
  | some i => D i - D i z • E

variable [DecidableEq ι]

/-- A transverse derivative extends the old dual frame to a dual frame
including the new hypersurface equation. -/
theorem transverseExtendedDerivations_dual
    (D : ι → Derivation k A A) (w : ι → A) (E : Derivation k A A) (z : A)
    (hD : ∀ i j, D i (w j) = if i = j then 1 else 0)
    (hEz : E z = 1) (hEw : ∀ i, E (w i) = 0) :
    ∀ i j, transverseExtendedDerivations D E z i (transverseExtendedCoordinates w z j) =
      if i = j then 1 else 0 := by
  intro i j
  cases i with
  | none =>
    cases j with
    | none =>
      change E z = _
      rw [ite_eq_left rfl]
      exact hEz
    | some j => simpa only [transverseExtendedDerivations, transverseExtendedCoordinates,
        reduceCtorEq, ite_false] using hEw j
  | some i =>
    cases j with
    | none => simp only [transverseExtendedDerivations, transverseExtendedCoordinates,
        Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul, hEz, mul_one,
        sub_self, reduceCtorEq, ite_false]
    | some j => simp only [transverseExtendedDerivations, transverseExtendedCoordinates,
        Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul, hEw, mul_zero,
        sub_zero, hD, Option.some.injEq]

variable [Fintype ι] [Algebra.Smooth k A]

/-- Actual étale coordinates simultaneously retain all boundary equations
and the transverse hypersurface equation around any point. -/
theorem exists_adapted_transverse_coordinates
    (D : ι → Derivation k A A) (w : ι → A) (E : Derivation k A A) (z : A)
    (hD : ∀ i j, D i (w j) = if i = j then 1 else 0)
    (hEz : E z = 1) (hEw : ∀ i, E (w i) = 0) (q : Ideal A) [q.IsPrime] :
    ∃ f ∉ q, ∃ (n : ℕ) (φ : MvPolynomial (Fin n ⊕ Option ι) k →+* Localization.Away f),
      φ.Etale ∧ (∀ r : k, φ (MvPolynomial.C r) = algebraMap k (Localization.Away f) r) ∧
      φ (MvPolynomial.X (Sum.inr none)) = algebraMap A (Localization.Away f) z ∧
      ∀ i, φ (MvPolynomial.X (Sum.inr (some i))) = algebraMap A (Localization.Away f) (w i) := by
  obtain ⟨f, hf, n, φ, hφ, hC, hX⟩ := exists_adapted_etale_frame
    (transverseExtendedDerivations D E z) (transverseExtendedCoordinates w z)
    (transverseExtendedDerivations_dual D w E z hD hEz hEw) q
  exact ⟨f, hf, n, φ, hφ, hC, hX none, fun i => hX (some i)⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedEtaleFrame.Construction
