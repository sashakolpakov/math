import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamProductNaturality

/-! # De Rham Additive Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamAdditiveProduct.Wedge

noncomputable section

/-! Additive maps with the actual differential-symbol formula preserve
the PD wedge. This also covers native coefficient-restriction maps. -/

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B]
  (I : Ideal A) (δI : DividedPowers I) (J : Ideal B) (δJ : DividedPowers J)
  (f : A →+* B)
  (F : ∀ n, AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δI n →+ AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form S B J δJ n)
  (hF : ∀ n a v, F n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δI a v) =
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol S B J δJ (f a) (f ∘ v))

include hF in
theorem addMap_wedge (p q : ℕ)
    (x : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δI p) (y : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δI q) :
    F (p + q) (DeRhamWedge.wedge R A I δI p q x y) =
      DeRhamWedge.wedge S B J δJ p q (F p x) (F q y) := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δI p).mkQ_surjective x
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A p).mkQ_surjective x
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | single v a =>
    obtain ⟨y, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δI q).mkQ_surjective y
    obtain ⟨y, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A q).mkQ_surjective y
    induction y using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add y z hy hz => simp only [map_add, hy, hz]
    | single w b =>
      change F (p + q) (DeRhamWedge.wedge R A I δI p q (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δI a v)
        (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δI b w)) =
        DeRhamWedge.wedge S B J δJ p q (F p (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δI a v))
          (F q (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δI b w))
      rw [DeRhamWedge.wedge_symbol, hF, hF, hF, DeRhamWedge.wedge_symbol, map_mul]
      congr 1
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamAdditiveProduct.Wedge
