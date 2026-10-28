import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KernelDetermination
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELTargetComparison

/-! # PEL Quotient Determination -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Equality of actual Tate preimages determines the complete PEL
quotient, including its polarization and normalized Poincare bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {R k : Type} [CommRing R] [Field k] [CharZero k] [IsAlgClosed k]
  {g N q m : ℕ} [Fact q.Prime]
  {P Q Q' : PEL.PELFamilyData R g N (Spec (.of k))}
  (e : PELIsogenies.PELIsogeny P Q (q ^ m)) (f : PELIsogenies.PELIsogeny P Q' (q ^ m))
  (δ : Fin g → ℕ) (hP : P.polarizationMap.HasPolarizationType δ)
  (hQ : Q.polarizationMap.HasPolarizationType δ)
  (hQ' : Q'.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))
  (h : Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom =
    Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom)

def PELIsogenies.PELIsogeny.quotientFamilyIsoOfPreimageEq : PELModuli.PELFamilyIso Q Q' :=
  Isogenies.NeighborCounting.PELTargetComparison.quotientPELIso e f
    (e.kernel_eq_all_tests_of_preimage_eq f δ hP hQ hQ' hq h)

theorem PELIsogenies.PELIsogeny.quotientFamilyIsoOfPreimageEq_factor :
    e.isogeny.hom ≫ (e.quotientFamilyIsoOfPreimageEq f δ hP hQ hQ' hq h).abelian.hom =
      f.isogeny.hom :=
  Isogenies.NeighborCounting.PELTargetComparison.quotientPELIso_projection e f
    (e.kernel_eq_all_tests_of_preimage_eq f δ hP hQ hQ' hq h)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
