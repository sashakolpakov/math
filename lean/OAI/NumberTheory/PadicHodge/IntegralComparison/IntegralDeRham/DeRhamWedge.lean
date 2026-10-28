import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.Wedge

/-! # De Rham Wedge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.DeRhamWedge

noncomputable section

/-! The native differential-symbol wedge product over every
commutative base ring. Both defining relation spans are killed before
the bilinear operation descends to the actual form modules. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

theorem rawWedge_relation_left_one {p q : ℕ} (r : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.RelationIndex R A p)
    (w : Fin q → A) :
    Wedge.rawWedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation R A p r) (Finsupp.single w 1) = 0 := by
  cases r with
  | add v i x y =>
      simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation, map_sub, LinearMap.sub_apply, Wedge.rawWedge_single, mul_one,
        Wedge.append_update_left]
      rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_update_add]
      abel
  | mul v i x y =>
      simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation, map_sub, LinearMap.sub_apply, Wedge.rawWedge_single, mul_one,
        Wedge.append_update_left]
      rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_update_mul, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one R A x, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one R A y]
      abel
  | base v i r =>
      simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation, Wedge.rawWedge_single, mul_one, Wedge.append_update_left]
      exact AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_update_base R A _ _ _
  | alt v i j hij hne =>
      simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation, Wedge.rawWedge_single, mul_one]
      exact AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_alt R A _ (i.castAdd q) (j.castAdd q)
        (by simpa only [Fin.append_left] using hij)
        (fun h => hne (Fin.ext (congrArg (fun z : Fin (p + q) => z.val) h)))

theorem rawWedge_relation_right_one {p q : ℕ} (v : Fin p → A)
    (r : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.RelationIndex R A q) :
    Wedge.rawWedge R A p q (Finsupp.single v 1) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation R A q r) = 0 := by
  cases r with
  | add w i x y =>
      simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation, map_sub, Wedge.rawWedge_single, one_mul, Wedge.append_update_right]
      rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_update_add]
      abel
  | mul w i x y =>
      simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation, map_sub, Wedge.rawWedge_single, one_mul, Wedge.append_update_right]
      rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_update_mul, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one R A x, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one R A y]
      abel
  | base w i r =>
      simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation, Wedge.rawWedge_single, one_mul, Wedge.append_update_right]
      exact AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_update_base R A _ _ _
  | alt w i j hij hne =>
      simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation, Wedge.rawWedge_single, one_mul]
      exact AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_alt R A _ (Fin.natAdd p i) (Fin.natAdd p j)
        (by simpa only [Fin.append_right] using hij)
        (fun h => hne (Fin.ext (Nat.add_left_cancel
          (congrArg (fun z : Fin (p + q) => z.val) h))))

theorem rawWedge_relation_left {p q : ℕ} (r : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.RelationIndex R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A q) :
    Wedge.rawWedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation R A p r) y = 0 := by
  induction y using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy, add_zero]
  | single w b =>
      rw [show Finsupp.single w b = b • Finsupp.single w 1 by simp,
        map_smul, rawWedge_relation_left_one, smul_zero]

theorem rawWedge_relation_right {p q : ℕ} (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A p) (r : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.RelationIndex R A q) :
    Wedge.rawWedge R A p q x (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relation R A q r) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | single v a =>
      rw [show Finsupp.single v a = a • Finsupp.single v 1 by simp,
        map_smul, LinearMap.smul_apply, rawWedge_relation_right_one, smul_zero]

theorem rawWedge_relations_left {p q : ℕ} (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A p)
    (hx : x ∈ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A q) : Wedge.rawWedge R A p q x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨r, rfl⟩ := hx
      exact rawWedge_relation_left R A r y
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add x z hx hz ihx ihz => rw [map_add, LinearMap.add_apply, ihx, ihz, add_zero]
  | smul a x hx ih => rw [map_smul, LinearMap.smul_apply, ih, smul_zero]

theorem rawWedge_relations_right {p q : ℕ} (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A q)
    (hy : y ∈ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A q) : Wedge.rawWedge R A p q x y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨r, rfl⟩ := hy
      exact rawWedge_relation_right R A x r
  | zero => exact map_zero _
  | add y z hy hz ihy ihz => rw [map_add, ihy, ihz, add_zero]
  | smul a y hy ih => rw [map_smul, ih, smul_zero]

def wedge (p q : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A (p + q) :=
  BilinearQuotient.lift₂ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A p) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A q) (Wedge.rawWedge R A p q)
    (fun x hx y => rawWedge_relations_left R A x hx y)
    (fun x y hy => rawWedge_relations_right R A x y hy)

theorem wedge_symbol (p q : ℕ) (a b : A) (v : Fin p → A) (w : Fin q → A) :
    wedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A (a * b) (Fin.append v w) := by
  change Wedge.rawWedge R A p q (Finsupp.single v a) (Finsupp.single w b) = _
  exact Wedge.rawWedge_single R A p q a b v w

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.DeRhamWedge
