import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ProductProperties

/-! # Reduction Cup Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReductionCupCoordinates.Intrinsic

noncomputable section

/-! The finite cup identity in the literal full reduction-map coordinates.
Only the definitions of its constituent maps are expanded here. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem change_cup {A B C : Type*} (op : A → B → C)
    {x x' : A} {y y' : B} {z z' : C}
    (h : z' = op x' y') (hz : z = z') (hx : x = x') (hy : y = y') :
    z = op x y := by
  cases hx
  cases hy
  exact hz.trans h

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] Cochain.CohomologyCup.cohomologyCup HomologicalComplex.homology

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

abbrev ordinary (i : ℕ) :=
  ((OrdinaryCechUnit.IntrinsicOrdinary.bicomplex p X).total (.up ℕ)).homology i

theorem cup (i j : ℕ) (x : ordinary p X i) (y : ordinary p X j) :
    ReductionProduct.Intrinsic.reductionComparison p X Y f hp n (i+j)
      (IntegralDeRham.CechProduct.cohomologyCup ℤ_[p] X
        (NonemptyCechNerve.nerve (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X)) i j x y) =
    Balanced.SmoothProperWittCup.cup p (ZMod p) Y n i j
      (ReductionProduct.Intrinsic.reductionComparison p X Y f hp n i x)
      (ReductionProduct.Intrinsic.reductionComparison p X Y f hp n j y) := by
  have h := ProductProperties.IntrinsicComparison.reductionComparison_cup p X Y f hp n i j x y
  refine change_cup (fun x y => Balanced.SmoothProperWittCup.cup p (ZMod p) Y n i j x y) h ?_ ?_ ?_
  · as_aux_lemma => rfl
  · as_aux_lemma => rfl
  · as_aux_lemma => rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReductionCupCoordinates.Intrinsic
