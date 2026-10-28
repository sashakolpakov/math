import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ResidueScalar

/-! # Residue Prime -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ResiduePrime

noncomputable section

/-! The prime induced by an actual residue-field point is its image under the global-functions map to the spectrum. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem residuePoint_prime_comap (S : Scheme.{u}) (x : S)
    (p : PrimeSpectrum Γ(Spec (S.residueField x), ⊤)) :
    p.comap (S.fromSpecResidueField x).appTop.hom = S.toSpecΓ x := by
  let : Field Γ(Spec (S.residueField x), ⊤) :=
    ((Scheme.ΓSpecIso (S.residueField x)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField (S.residueField x))).toField
  let y : Spec (S.residueField x) := default
  have hp : (Spec (S.residueField x)).toSpecΓ y = p := by
    apply PrimeSpectrum.ext
    let q : PrimeSpectrum Γ(Spec (S.residueField x), ⊤) := (Spec (S.residueField x)).toSpecΓ y
    have : q.asIdeal.IsPrime := q.isPrime
    exact q.asIdeal.eq_bot_of_prime.trans p.asIdeal.eq_bot_of_prime.symm
  have h := congrArg (fun k : Spec (S.residueField x) ⟶ Spec Γ(S, ⊤) => k y)
    (Scheme.toSpecΓ_naturality (S.fromSpecResidueField x))
  change S.toSpecΓ (S.fromSpecResidueField x y) =
    ((Spec (S.residueField x)).toSpecΓ y).comap (S.fromSpecResidueField x).appTop.hom at h
  rw [Scheme.fromSpecResidueField_apply, hp] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ResiduePrime
