import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedScalarFraction

/-! # Refined Scalar Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedScalarCoordinates

noncomputable section

/-! Bundled normalization with both genuine refinement legs and the
canonical scalar value of the fraction's ordered numerator. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  {L K F : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (eP : HomotopyEquiv L (KoszulPartial.Components.coefficient R P (Fin.append s t)))
  (eN : HomotopyEquiv K (KoszulPartial.Components.coefficient R P s))
  (eF : HomotopyEquiv F (KoszulPartial.Components.coefficient R P s)) (r : L ⟶ K) (l : F ⟶ K)
  (hr : Homotopy (r ≫ eN.hom) (eP.hom ≫ DuplicateFraction.normalMap R s t P))
  (hl : Homotopy (l ≫ eN.hom) eF.hom)
  (k : Type u) [CommRing k] [Algebra k R]
  (hP : Function.Bijective (algebraMap R (P.obj (op (⊤_ C)))))
  (d : ℕ) (hL : ∀ q, q ≠ d → L.ExactAt q)
  (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q,
    IsZero ((((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) d).obj (L.homology d)).X p).obj
      (op ((AugmentedOrdered.Cech.formal U q).obj a))))
  (e₀ : (R ⧸ OrientedTopCohomology.ideal R (Fin.append s t)) ≃ₐ[k] k)

abbrev comparison (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L) :=
  And.intro (Supported.CechHomotopyEquivalence.refinementIso_hom U eF eN l hl (c+m))
    (And.intro (RefinedScalarFraction.fraction R P U s t ht eP eN eF r hr
      k hP d hL hzero e₀ y)
      (RefinedScalarFraction.evaluation R P U s t eP k hP d hL hzero e₀ y))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedScalarCoordinates
