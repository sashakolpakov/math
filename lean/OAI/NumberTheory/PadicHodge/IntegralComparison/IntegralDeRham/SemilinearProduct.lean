import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.DeRhamWedge
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearA

/-! # Semilinear Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.SemilinearProduct.Wedge

noncomputable section

/-! Simultaneous change of the base ring and coefficients preserves the
integral product on the original differential-symbol presentation. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] (σ : R →+* S) (f : A →+* B)
  (h : ∀ r, f (algebraMap R A r) = algebraMap S B (σ r))

theorem semilinearMap_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearA.DeRhamSemilinearMap.formMap R S A B σ f h (p + q) (DeRhamWedge.wedge R A p q x y) =
      DeRhamWedge.wedge S B p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearA.DeRhamSemilinearMap.formMap R S A B σ f h p x)
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearA.DeRhamSemilinearMap.formMap R S A B σ f h q y) := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A p).mkQ_surjective x
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | single v a =>
    obtain ⟨y, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A q).mkQ_surjective y
    induction y using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add y z hy hz => simp only [map_add, hy, hz]
    | single w b =>
      change AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearA.DeRhamSemilinearMap.formMap R S A B σ f h (p + q)
        (DeRhamWedge.wedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w)) =
          DeRhamWedge.wedge S B p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearA.DeRhamSemilinearMap.formMap R S A B σ f h p (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v))
            (AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearA.DeRhamSemilinearMap.formMap R S A B σ f h q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w))
      rw [DeRhamWedge.wedge_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearA.DeRhamSemilinearMap.formMap_symbol,
        AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearA.DeRhamSemilinearMap.formMap_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearA.DeRhamSemilinearMap.formMap_symbol,
        DeRhamWedge.wedge_symbol, map_mul]
      congr 1
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.SemilinearProduct.Wedge
