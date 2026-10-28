import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MultiplicationPELIsogeny
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsoPreimages
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexIsogenyDetermination

/-! # Multiplication Factor Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! A marked polarized isogeny with the multiplication lattice is
literally multiplication followed by its target-family comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {R k : Type} [CommRing R] [Field k] [CharZero k] [IsAlgClosed k]
  {g N q : ℕ} [Fact q.Prime]
  {P Q : PEL.PELFamilyData R g N (Spec (.of k))} (hqN : Nat.Coprime q N)
  (j : PELModuli.PELFamilyIso (P.shiftMarking (ZMod.unitOfCoprime q hqN)) Q)

def PELIsogenies.PELIsogeny.multiplicationCompared : PELIsogenies.PELIsogeny P Q (q ^ 2) :=
  ((P.multiplicationPELIsogeny q hqN).comp j.toIsogeny).castMultiplier (Nat.mul_one (q ^ 2))

theorem PELIsogenies.PELIsogeny.multiplicationCompared_hom :
    (PELIsogenies.PELIsogeny.multiplicationCompared hqN j).isogeny.hom = ((𝟙 P.abelian.scheme) ^ q) ≫ j.abelian.hom :=
  PELIsogenies.PELIsogeny.castMultiplier_hom (Nat.mul_one (q ^ 2)) _

theorem PELIsogenies.PELIsogeny.multiplicationCompared_preimage :
    Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) (PELIsogenies.PELIsogeny.multiplicationCompared hqN j).isogeny.hom =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) ((𝟙 P.abelian.scheme) ^ q) := by
  simp only [PELIsogenies.PELIsogeny.multiplicationCompared_hom]
  exact IsoPreimages.isogenyTatePreimage_comp_iso _ q _ j.abelian

theorem PELIsogenies.PELIsogeny.hom_eq_multiplication_of_preimage (e : PELIsogenies.PELIsogeny P Q (q ^ 2))
    (δ : Fin g → ℕ) (hP : P.polarizationMap.HasPolarizationType δ)
    (hQ : Q.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))
    (he : Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) ((𝟙 P.abelian.scheme) ^ q))
    (hr : ∀ a : PELModuli.PELFamilyIso Q Q, a.abelian.hom = 𝟙 Q.abelian.scheme) :
    e.isogeny.hom = ((𝟙 P.abelian.scheme) ^ q) ≫ j.abelian.hom := by
  have h := e.eq_of_preimage_eq_of_rigid (PELIsogenies.PELIsogeny.multiplicationCompared hqN j) δ hP hQ hq
    (he.trans (PELIsogenies.PELIsogeny.multiplicationCompared_preimage hqN j).symm) hr
  exact (congrArg (fun f => f.isogeny.hom) h).trans (PELIsogenies.PELIsogeny.multiplicationCompared_hom hqN j)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
