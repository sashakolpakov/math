import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELQuotientDetermination
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexPELRigidity
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenyExt

/-! # Complex Isogeny Determination -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexIsogenyDetermination.PELIsogeny

noncomputable section

/-! Equal Tate preimages give equality of actual marked polarized
isogenies with the same complex target, without quotienting their maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

section General

variable {R k : Type} [CommRing R] [Field k] [CharZero k] [IsAlgClosed k]
  {g N q m : ℕ} [Fact q.Prime]
  {P Q : PEL.PELFamilyData R g N (Spec (.of k))}

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.eq_of_preimage_eq_of_rigid (e f : PELIsogenies.PELIsogeny P Q (q ^ m))
    (δ : Fin g → ℕ) (hP : P.polarizationMap.HasPolarizationType δ)
    (hQ : Q.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))
    (h : Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom)
    (hr : ∀ j : PELModuli.PELFamilyIso Q Q, j.abelian.hom = 𝟙 Q.abelian.scheme) : e = f := by
  let j := e.quotientFamilyIsoOfPreimageEq f δ hP hQ hQ hq h
  have hj := hr j
  have hf := e.quotientFamilyIsoOfPreimageEq_factor f δ hP hQ hQ hq h
  change e.isogeny.hom ≫ j.abelian.hom = f.isogeny.hom at hf
  apply PELIsogenies.PELIsogeny.eq_of_hom_eq
  simpa only [hj, Category.comp_id] using hf

end General

local notation "fiberBase" => Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField))

variable {R : Type} [CommRing R] {g N q m : ℕ} [Fact q.Prime]
  {δ : Fin g → ℕ} {c : R →+* R}
  {P Q : PEL.PELFamilyData R g N fiberBase}

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.complex_eq_of_factor_iso {n : ℕ} (e f : PELIsogenies.PELIsogeny P Q n)
    (j : PELModuli.PELFamilyIso Q Q) (hQ : Q.IsPEL δ c) (hN : 3 ≤ N)
    (hf : e.isogeny.hom ≫ j.abelian.hom = f.isogeny.hom) : e = f := by
  have hj := PELModuli.PELFamilyIso.complex_abelian_eq_id_ofBase (S := fiberBase) rfl j hQ hN
  apply PELIsogenies.PELIsogeny.eq_of_hom_eq
  simpa only [hj, Category.comp_id] using hf

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.complex_eq_of_preimage_eq (e f : PELIsogenies.PELIsogeny P Q (q ^ m))
    (hP : P.IsPEL δ c) (hQ : Q.IsPEL δ c)
    (hq : Nat.Coprime q (∏ i, δ i)) (hN : 3 ≤ N)
    (h : Rational.isogenyTatePreimage (T := Over.mk (𝟙 fiberBase)) (q := q) e.isogeny.hom =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 fiberBase)) (q := q) f.isogeny.hom) : e = f := by
  apply PELIsogenies.PELIsogeny.eq_of_preimage_eq_of_rigid e f δ hP.1 hQ.1 hq h
  intro j
  exact PELModuli.PELFamilyIso.complex_abelian_eq_id_ofBase (S := fiberBase) rfl j hQ hN

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexIsogenyDetermination.PELIsogeny
