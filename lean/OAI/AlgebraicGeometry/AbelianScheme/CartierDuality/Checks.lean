import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

/-! # Checks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Checks

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Exact full Cartier-duality proposition exposed by this entrypoint. -/
theorem cartier_duality_fullSpecification
    {S : Scheme.{u}} (G : CartierDuality.PolarizedTorsion.FppfAb S)
    (hG : CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable G) :
    CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable (CartierDuality.PolarizedTorsion.cartierDual G) ∧
      CartierDuality.PolarizedTorsion.IsPerfectPairing (CartierDuality.PolarizedTorsion.cartierEvaluation G) ∧
      IsIso (CartierDuality.PolarizedTorsion.bidualEvaluation G) ∧
      (∀ (T : Scheme.{u}) (f : T ⟶ S),
        IsIso (CartierDuality.PolarizedTorsion.dualBaseChangeComparison f G)) :=
  CartierDuality.PolarizedTorsion.cartier_duality G hG

/-- Exact full polarization, block, and annihilator proposition exposed by this entrypoint. -/
theorem polarization_blocks_and_annihilators_fullSpecification
    {S : Scheme.{u}} (A : CartierDuality.PolarizedTorsion.AbelianScheme S) (ell : CartierDuality.PolarizedTorsion.Polarization A)
    (n : ℕ) (hn : 0 < n)
    (hdegree : ∀ s : S, Nat.Coprime n (ell.fiberDegree s))
    (I : Type u) [Fintype I] (conj : I → I)
    (hconj : Function.Involutive conj)
    (B : CartierDuality.PolarizedTorsion.TorsionBlockDecomposition A n I)
    (hadjoint : ∀ i : I,
      CartierDuality.PolarizedTorsion.ProjectorsAdjoint (ell.torsionPairing n hn)
        (B.projector i) (B.projector (conj i)))
    (i : I) (H : Subobject (B.block i))
    (hH : CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable (H : CartierDuality.PolarizedTorsion.FppfAb S)) :
    let e := B.restrictedPairing (ell.torsionPairing n hn) i (conj i)
    CartierDuality.PolarizedTorsion.IsPerfectPairing e ∧
      CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable (CartierDuality.PolarizedTorsion.annihilator e H : CartierDuality.PolarizedTorsion.FppfAb S) ∧
      IsIso (CartierDuality.PolarizedTorsion.annihilatorToQuotientDual e H) ∧
      CartierDuality.PolarizedTorsion.annihilator e.flip (CartierDuality.PolarizedTorsion.annihilator e H) = H ∧
      (∀ (T : Scheme.{u}) (f : T ⟶ S),
        CartierDuality.PolarizedTorsion.baseChangeSubobject f (CartierDuality.PolarizedTorsion.annihilator e H) =
          CartierDuality.PolarizedTorsion.annihilator (CartierDuality.PolarizedTorsion.baseChangePairing f e) (CartierDuality.PolarizedTorsion.baseChangeSubobject f H)) :=
  CartierDuality.PolarizedTorsion.polarization_blocks_and_annihilators
    A ell n hn hdegree I conj hconj B hadjoint i H hH

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Checks
