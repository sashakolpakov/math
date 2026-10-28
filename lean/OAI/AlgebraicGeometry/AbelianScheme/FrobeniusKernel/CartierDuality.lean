import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityCanonical

/-! # Cartier Duality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDuality.Construction

/-! The full CartierDuality consumer proposition at
7356dce03dea25469fafa1fb39a3e9b53681acc9, available as an explicit conditional
graph input. Neither block perfection nor an annihilator comparison for the
FrobeniusKernel source is assumed separately. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def FullCartierDualityInput : Prop :=
  (∀ {S : Scheme.{u}} (G : CartierDuality.PolarizedTorsion.FppfAb S) (_hG : CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable G),
    CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable (CartierDuality.PolarizedTorsion.cartierDual G) ∧
      CartierDuality.PolarizedTorsion.IsPerfectPairing (CartierDuality.PolarizedTorsion.cartierEvaluation G) ∧
      IsIso (CartierDuality.PolarizedTorsion.bidualEvaluation G) ∧
      ∀ (T : Scheme.{u}) (f : T ⟶ S), IsIso (CartierDuality.PolarizedTorsion.dualBaseChangeComparison f G)) ∧
  (∀ {S : Scheme.{u}} (A : CartierDuality.PolarizedTorsion.AbelianScheme S) (ell : CartierDuality.PolarizedTorsion.Polarization A)
    (n : ℕ) (hn : 0 < n) (_hdegree : ∀ s : S, Nat.Coprime n (CartierDuality.PolarizedTorsion.Polarization.fiberDegree ell s))
    (I : Type u) [Fintype I] (conj : I → I) (_hconj : Function.Involutive conj)
    (B : CartierDuality.PolarizedTorsion.TorsionBlockDecomposition A n I)
    (_hadjoint : ∀ i : I, CartierDuality.PolarizedTorsion.ProjectorsAdjoint (CartierDuality.PolarizedTorsion.Polarization.torsionPairing ell n hn)
      (B.projector i) (B.projector (conj i)))
    (i : I) (H : Subobject (B.block i)) (_hH : CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable (H : CartierDuality.PolarizedTorsion.FppfAb S)),
    let e := B.restrictedPairing (CartierDuality.PolarizedTorsion.Polarization.torsionPairing ell n hn) i (conj i)
    CartierDuality.PolarizedTorsion.IsPerfectPairing e ∧
      CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable (CartierDuality.PolarizedTorsion.annihilator e H : CartierDuality.PolarizedTorsion.FppfAb S) ∧
      IsIso (CartierDuality.PolarizedTorsion.annihilatorToQuotientDual e H) ∧
      CartierDuality.PolarizedTorsion.annihilator e.flip (CartierDuality.PolarizedTorsion.annihilator e H) = H ∧
      ∀ (T : Scheme.{u}) (f : T ⟶ S),
        CartierDuality.PolarizedTorsion.baseChangeSubobject f (CartierDuality.PolarizedTorsion.annihilator e H) =
          CartierDuality.PolarizedTorsion.annihilator (CartierDuality.PolarizedTorsion.baseChangePairing f e) (CartierDuality.PolarizedTorsion.baseChangeSubobject f H))

/-- The accepted complete CartierDuality development supplies the entire graph input. -/
theorem fullCartierDualityInput_proved : FullCartierDualityInput :=
  ⟨CartierDuality.PolarizedTorsion.cartier_duality, CartierDuality.PolarizedTorsion.polarization_blocks_and_annihilators⟩

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDuality.Construction
