import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.WedgeNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham

/-! # De Rham Wedge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamWedge

noncomputable section

/-! The integral native wedge descends through the actual divided-power
differential relations in each argument. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

def projectedWedge (p q : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q →ₗ[A]
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ (p + q) :=
  (IntegralDeRham.DeRhamWedge.wedge R A p q).compr₂ (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ (p + q)).mkQ

theorem projectedWedge_symbol (p q : ℕ) (a b : A) (v : Fin p → A) (w : Fin q → A) :
    projectedWedge R A I δ p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ (a * b) (Fin.append v w) := by
  change (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ (p + q)).mkQ
    (IntegralDeRham.DeRhamWedge.wedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w)) = _
  rw [IntegralDeRham.DeRhamWedge.wedge_symbol]
  rfl

theorem relation_left_one {p q : ℕ} (r : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.RelationIndex A I p) (w : Fin q → A) :
    projectedWedge R A I δ p q (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relation R A I δ p r) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 w) = 0 := by
  simp only [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relation, map_sub, LinearMap.sub_apply, projectedWedge_symbol,
    mul_one, IntegralDeRham.Wedge.append_update_left]
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol_update_dpow,
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol_smul_one R A I δ (δ.dpow r.m r.x), sub_self]

theorem relation_right_one {p q : ℕ} (v : Fin p → A) (r : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.RelationIndex A I q) :
    projectedWedge R A I δ p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 v) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relation R A I δ q r) = 0 := by
  simp only [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relation, map_sub, projectedWedge_symbol,
    one_mul, IntegralDeRham.Wedge.append_update_right]
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol_update_dpow,
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol_smul_one R A I δ (δ.dpow r.m r.x), sub_self]

theorem relation_left {p q : ℕ} (r : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.RelationIndex A I p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    projectedWedge R A I δ p q (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relation R A I δ p r) y = 0 := by
  obtain ⟨y, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A q).mkQ_surjective y
  induction y using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add y z hy hz => simp only [map_add, hy, hz, add_zero]
  | single w b =>
      change projectedWedge R A I δ p q (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relation R A I δ p r) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w) = 0
      rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one, map_smul, relation_left_one, smul_zero]

theorem relation_right {p q : ℕ} (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (r : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.RelationIndex A I q) :
    projectedWedge R A I δ p q x (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relation R A I δ q r) = 0 := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A p).mkQ_surjective x
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, add_zero]
  | single v a =>
      change projectedWedge R A I δ p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relation R A I δ q r) = 0
      rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one, map_smul, LinearMap.smul_apply, relation_right_one, smul_zero]

theorem relations_left {p q : ℕ} (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p)
    (hx : x ∈ AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    projectedWedge R A I δ p q x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨r, rfl⟩ := hx
      exact relation_left R A I δ r y
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x z hx hz ihx ihz => rw [map_add, LinearMap.add_apply, ihx, ihz, add_zero]
  | smul a x hx ih => rw [map_smul, LinearMap.smul_apply, ih, smul_zero]

theorem relations_right {p q : ℕ} (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q)
    (hy : y ∈ AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ q) :
    projectedWedge R A I δ p q x y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨r, rfl⟩ := hy
      exact relation_right R A I δ x r
  | zero => exact map_zero _
  | add y z hy hz ihy ihz => rw [map_add, ihy, ihz, add_zero]
  | smul a y hy ih => rw [map_smul, ih, smul_zero]

def wedge (p q : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ p →ₗ[A]
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ q →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ (p + q) :=
  BilinearQuotient.lift₂ (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ p) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ q)
    (projectedWedge R A I δ p q)
    (fun x hx y => relations_left R A I δ x hx y)
    (fun x y hy => relations_right R A I δ x y hy)

theorem quotient_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    wedge R A I δ p q ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ p).mkQ x)
        ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ q).mkQ y) =
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ (p + q)).mkQ (IntegralDeRham.DeRhamWedge.wedge R A p q x y) := rfl

theorem wedge_symbol (p q : ℕ) (a b : A) (v : Fin p → A) (w : Fin q → A) :
    wedge R A I δ p q (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ a v) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ b w) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ (a * b) (Fin.append v w) :=
  projectedWedge_symbol R A I δ p q a b v w

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamWedge
