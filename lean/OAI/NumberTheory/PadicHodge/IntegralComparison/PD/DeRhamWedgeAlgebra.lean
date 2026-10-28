import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamLeibniz
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.WedgeAlgebra

/-! # De Rham Wedge Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamWedgeAlgebra

noncomputable section

/-! The product on the original divided-power de Rham complex is
associative and has the original constant-one symbol as a closed unit. -/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

theorem wedge_assoc {p q r : ℕ}
    (x : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ p) (y : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ q)
    (z : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ r) :
    DeRhamLeibniz.Wedge.degreeCast R A I δ (Nat.add_assoc p q r)
        (DeRhamWedge.wedge R A I δ (p + q) r (DeRhamWedge.wedge R A I δ p q x y) z) =
      DeRhamWedge.wedge R A I δ p (q + r) x (DeRhamWedge.wedge R A I δ q r y z) := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ p).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ q).mkQ_surjective y
  obtain ⟨z, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ r).mkQ_surjective z
  simp only [DeRhamWedge.quotient_wedge, ← DeRhamLeibniz.Wedge.quotient_degreeCast, IntegralDeRham.WedgeAlgebra.wedge_assoc]

def unitForm : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ 0 := AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ 1 (fun i => i.elim0)

theorem quotient_unit :
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ 0).mkQ (IntegralDeRham.WedgeAlgebra.unitForm R A) =
      unitForm R A I δ := rfl

theorem unit_wedge {p : ℕ} (x : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ p) :
    DeRhamLeibniz.Wedge.degreeCast R A I δ (Nat.zero_add p) (DeRhamWedge.wedge R A I δ 0 p (unitForm R A I δ) x) = x := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ p).mkQ_surjective x
  rw [← quotient_unit, DeRhamWedge.quotient_wedge, ← DeRhamLeibniz.Wedge.quotient_degreeCast,
    IntegralDeRham.WedgeAlgebra.unit_wedge]

theorem wedge_unit {p : ℕ} (x : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ p) :
    DeRhamWedge.wedge R A I δ p 0 x (unitForm R A I δ) = x := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ p).mkQ_surjective x
  rw [← quotient_unit, DeRhamWedge.quotient_wedge, IntegralDeRham.WedgeAlgebra.wedge_unit]
  rfl

theorem differential_unit : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ 0 (unitForm R A I δ) = 0 := by
  rw [← quotient_unit, AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential_mk, IntegralDeRham.WedgeAlgebra.differential_unit, map_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamWedgeAlgebra
