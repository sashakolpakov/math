import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SpecialKernelPresentations

/-! # Factor Squares -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting

/-! Equality and actual carrier isomorphisms of subgroup presentations
preserve their factorization criterion on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Kernel.FactorSquares.factor_iff_of_carrier_iso {C : Type*} [Category C] {H H' A T : C}
    (e : H ≅ H') (i : H ⟶ A) (j : H' ⟶ A) (h : e.hom ≫ j = i) (a : T ⟶ A) :
    (∃ z : T ⟶ H, z ≫ i = a) ↔ ∃ z : T ⟶ H', z ≫ j = a := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z ≫ e.hom, (Category.assoc z e.hom j).trans
      ((congrArg (fun f => z ≫ f) h).trans hz)⟩
  · rintro ⟨z, hz⟩
    have hi : e.inv ≫ i = j :=
      (congrArg (fun f => e.inv ≫ f) h.symm).trans (e.inv_hom_id_assoc j)
    exact ⟨z ≫ e.inv, (Category.assoc z e.inv i).trans
      ((congrArg (fun f => z ≫ f) hi).trans hz)⟩

theorem Intrinsic.Neighbors.KernelPresentation.factor_iff_of_eq {S : Scheme} {A B : Over S}
    (P Q : Intrinsic.Neighbors.KernelPresentation A) (h : P = Q) (i : A ⟶ B) (T : Over S) (a : T ⟶ B) :
    (∃ z : T ⟶ P.carrier, z ≫ P.inclusion ≫ i = a) ↔
      ∃ z : T ⟶ Q.carrier, z ≫ Q.inclusion ≫ i = a :=
  Iff.of_eq (congrArg (fun K : Intrinsic.Neighbors.KernelPresentation A =>
    ∃ z : T ⟶ K.carrier, z ≫ K.inclusion ≫ i = a) h)

theorem Intrinsic.Neighbors.KernelPresentation.factor_pullback_comp {S T : Scheme} {A B : Over S}
    (P : Intrinsic.Neighbors.KernelPresentation A) (b : T ⟶ S) (i : A ⟶ B) (U : Over T)
    (a : U ⟶ (Over.pullback b).obj B) :
    (∃ z : U ⟶ (Over.pullback b).obj P.carrier,
      z ≫ (Over.pullback b).map (P.inclusion ≫ i) = a) ↔
      ∃ z : U ⟶ (P.pullback b).carrier,
        z ≫ (P.pullback b).inclusion ≫ (Over.pullback b).map i = a := by
  change (∃ z : U ⟶ (Over.pullback b).obj P.carrier,
    z ≫ (Over.pullback b).map (P.inclusion ≫ i) = a) ↔
      ∃ z : U ⟶ (Over.pullback b).obj P.carrier,
        z ≫ (Over.pullback b).map P.inclusion ≫ (Over.pullback b).map i = a
  rw [(Over.pullback b).map_comp]

end AlgebraicGeometry.Isogenies.NeighborCounting

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FactorSquares

/-! An actual carrier comparison and an ambient inclusion comparison
give the same all-test factorization criterion in the final source. -/

open _root_.CategoryTheory

theorem factor_iff_of_two_squares {C : Type*} [Category C] {H H' A B D T : C}
    (e : H ≅ H') (i : H ⟶ A) (j : H' ⟶ B) (a : A ⟶ B)
    (b : B ⟶ D) (c : A ⟶ D)
    (h : e.hom ≫ j = i ≫ a) (ha : a ≫ b = c) (x : T ⟶ D) :
    (∃ z : T ⟶ H, z ≫ i ≫ c = x) ↔ ∃ z : T ⟶ H', z ≫ j ≫ b = x := by
  have hs : e.hom ≫ (j ≫ b) = i ≫ c :=
    (Category.assoc e.hom j b).symm.trans
      ((congrArg (fun f => f ≫ b) h).trans
        ((Category.assoc i a b).trans (congrArg (fun f => i ≫ f) ha)))
  exact factor_iff_of_carrier_iso e (i ≫ c) (j ≫ b) hs x

end AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FactorSquares

end

end OAI
