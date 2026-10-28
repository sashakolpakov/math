import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.Leibniz

/-! # Wedge Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.WedgeAlgebra

noncomputable section

/-! Associativity and the closed unit for the native differential-symbol
product, without assumptions that factorials are invertible. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

theorem wedge_assoc {p q r : ℕ} (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) (z : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A r) :
    WedgeSigns.degreeCast R A (Nat.add_assoc p q r) (DeRhamWedge.wedge R A (p + q) r (DeRhamWedge.wedge R A p q x y) z) =
      DeRhamWedge.wedge R A p (q + r) x (DeRhamWedge.wedge R A q r y z) := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A p).mkQ_surjective x
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x t hx ht => simp only [map_add, LinearMap.add_apply, hx, ht]
  | single v a =>
    obtain ⟨y, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A q).mkQ_surjective y
    induction y using Finsupp.induction_linear with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add y t hy ht => simp only [map_add, LinearMap.add_apply, hy, ht]
    | single w b =>
      obtain ⟨z, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A r).mkQ_surjective z
      induction z using Finsupp.induction_linear with
      | zero => simp only [map_zero]
      | add z t hz ht => simp only [map_add, hz, ht]
      | single s c =>
        change WedgeSigns.degreeCast R A (Nat.add_assoc p q r)
          (DeRhamWedge.wedge R A (p + q) r (DeRhamWedge.wedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w))
            (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A c s)) =
          DeRhamWedge.wedge R A p (q + r) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)
            (DeRhamWedge.wedge R A q r (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A c s))
        simp only [DeRhamWedge.wedge_symbol, WedgeSigns.degreeCast_symbol, mul_assoc, Fin.append_assoc,
          Function.comp_apply]
        rfl

def unitForm : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 0 := AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 (fun i => i.elim0)

theorem unit_wedge {p : ℕ} (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) :
    WedgeSigns.degreeCast R A (Nat.zero_add p) (DeRhamWedge.wedge R A 0 p (unitForm R A) x) = x := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A p).mkQ_surjective x
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x z hx hz => simp only [map_add, hx, hz]
  | single v a =>
    change WedgeSigns.degreeCast R A (Nat.zero_add p)
      (DeRhamWedge.wedge R A 0 p (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 Fin.elim0) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v
    simp only [DeRhamWedge.wedge_symbol, WedgeSigns.degreeCast_symbol, one_mul, Fin.elim0_append,
      Function.comp_apply]
    rfl

theorem wedge_unit {p : ℕ} (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) : DeRhamWedge.wedge R A p 0 x (unitForm R A) = x := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A p).mkQ_surjective x
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | single v a =>
    change DeRhamWedge.wedge R A p 0 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 Fin.elim0) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v
    simp only [DeRhamWedge.wedge_symbol, mul_one, Fin.append_elim0, Function.comp_def, Fin.cast_refl]
    rfl

theorem differential_unit : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A 0 (unitForm R A) = 0 := by
  rw [unitForm, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_cons_one]

theorem unit_eq_rational : unitForm R A = RationalDeRham.WedgeAlgebra.unitForm R A := rfl

theorem degreeCast_eq_rational {m n : ℕ} (h : m = n) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A m) :
    WedgeSigns.degreeCast R A h x = RationalDeRham.Wedge.degreeCast R A h x := by
  subst n
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.WedgeAlgebra
