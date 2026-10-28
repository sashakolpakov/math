import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Checks

/-! # Cartier Duality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierDuality.Construction

/-!
The complete implemented CartierDuality prerequisite, including arbitrary-base
Cartier duality and the actual polarization-induced Weil pairing.
Neither ambient nor block perfection is added to its hypotheses.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

universe u

def CartierInput : Prop :=
  ∀ {S : Scheme.{u}} (G : CartierDuality.PolarizedTorsion.FppfAb S) (_hG : CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable G),
    CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable (CartierDuality.PolarizedTorsion.cartierDual G) ∧
      CartierDuality.PolarizedTorsion.IsPerfectPairing (CartierDuality.PolarizedTorsion.cartierEvaluation G) ∧
      IsIso (CartierDuality.PolarizedTorsion.bidualEvaluation G) ∧
      (∀ (T : Scheme.{u}) (f : T ⟶ S), IsIso (CartierDuality.PolarizedTorsion.dualBaseChangeComparison f G))

def PolarizationInput : Prop :=
  ∀ {S : Scheme.{u}} (A : CartierDuality.PolarizedTorsion.AbelianScheme S) (ell : CartierDuality.PolarizedTorsion.Polarization A)
    (n : ℕ) (hn : 0 < n) (_hdegree : ∀ s : S, Nat.Coprime n (ell.fiberDegree s))
    (I : Type u) [Fintype I] (conj : I → I) (_hconj : Function.Involutive conj)
    (B : CartierDuality.PolarizedTorsion.TorsionBlockDecomposition A n I)
    (_hadjoint : ∀ i : I, CartierDuality.PolarizedTorsion.ProjectorsAdjoint (ell.torsionPairing n hn)
      (B.projector i) (B.projector (conj i)))
    (i : I) (H : Subobject (B.block i)) (_hH : CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable (H : CartierDuality.PolarizedTorsion.FppfAb S)),
    let e := B.restrictedPairing (ell.torsionPairing n hn) i (conj i)
    CartierDuality.PolarizedTorsion.IsPerfectPairing e ∧
      CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable (CartierDuality.PolarizedTorsion.annihilator e H : CartierDuality.PolarizedTorsion.FppfAb S) ∧
      IsIso (CartierDuality.PolarizedTorsion.annihilatorToQuotientDual e H) ∧
      CartierDuality.PolarizedTorsion.annihilator e.flip (CartierDuality.PolarizedTorsion.annihilator e H) = H ∧
      (∀ (T : Scheme.{u}) (f : T ⟶ S),
        CartierDuality.PolarizedTorsion.baseChangeSubobject f (CartierDuality.PolarizedTorsion.annihilator e H) =
          CartierDuality.PolarizedTorsion.annihilator (CartierDuality.PolarizedTorsion.baseChangePairing f e) (CartierDuality.PolarizedTorsion.baseChangeSubobject f H))

def CartierDualityInput : Prop := CartierInput.{u} ∧ PolarizationInput.{u}

/-- Both complete prerequisite clauses are discharged by CartierDuality's proved native implementation. -/
theorem verified_CartierDualityInput : CartierDualityInput :=
  ⟨CartierDuality.PolarizedTorsion.cartier_duality, CartierDuality.PolarizedTorsion.polarization_blocks_and_annihilators⟩

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierDuality.Construction
