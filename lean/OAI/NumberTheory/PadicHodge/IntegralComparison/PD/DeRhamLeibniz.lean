import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamWedge
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.Leibniz

/-! # De Rham Leibniz -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamLeibniz.Wedge

noncomputable section

/-! The differential on the original divided-power forms is a graded
derivation for the integral symbol wedge. -/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

def degreeCast {m n : ℕ} (h : m = n) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ m ≃ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n := by
  subst n
  exact LinearEquiv.refl _ _

theorem quotient_degreeCast {m n : ℕ} (h : m = n)
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A m) :
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ n).mkQ (IntegralDeRham.WedgeSigns.degreeCast R A h x) =
      degreeCast R A I δ h ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ m).mkQ x) := by
  subst n
  rfl

theorem differential_wedge (p q : ℕ)
    (x : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ p) (y : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ q) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ (p + q) (DeRhamWedge.wedge R A I δ p q x y) =
      degreeCast R A I δ (by omega : (p + 1) + q = p + q + 1)
        (DeRhamWedge.wedge R A I δ (p + 1) q (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ p x) y) +
      (-1 : ℤ) ^ p • degreeCast R A I δ (by omega : p + (q + 1) = p + q + 1)
        (DeRhamWedge.wedge R A I δ p (q + 1) x (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ q y)) := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ p).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ q).mkQ_surjective y
  rw [DeRhamWedge.quotient_wedge, AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential_mk, IntegralDeRham.Leibniz.Wedge.differential_wedge,
    map_add, map_zsmul, quotient_degreeCast, quotient_degreeCast,
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential_mk, AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential_mk, DeRhamWedge.quotient_wedge, DeRhamWedge.quotient_wedge]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamLeibniz.Wedge
