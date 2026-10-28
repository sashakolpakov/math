import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedCoefficientFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedScalarFraction

/-! # Refined Coefficient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedCoefficientCoordinates

noncomputable section

/-! Both genuine refinement legs and the common point scalar are
retained in coefficient evaluation. -/
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
  {L K F T : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (eP : HomotopyEquiv L (KoszulPartial.Components.coefficient R P (Fin.append s t)))
  (eN : HomotopyEquiv K T) (eF : HomotopyEquiv F T)
  (r : L ⟶ K) (l : F ⟶ K)
  (δ : KoszulPartial.Components.coefficient R P (Fin.append s t) ⟶ T) (ev : T ⟶ KoszulPartial.Components.coefficient R P s)
  (hr : Homotopy (r ≫ eN.hom) (eP.hom ≫ δ))
  (hl : Homotopy (l ≫ eN.hom) eF.hom)
  (w : R) (he : Homotopy (δ ≫ ev) (w • DuplicateFraction.normalMap R s t P))
  (k : Type u) [CommRing k] [Algebra k R]
  (hP : Function.Bijective (algebraMap R (P.obj (op (⊤_ C)))))
  (d : ℕ) (hL : ∀ q, q ≠ d → L.ExactAt q)
  (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q,
    IsZero ((((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) d).obj (L.homology d)).X p).obj
      (op ((AugmentedOrdered.Cech.formal U q).obj a))))
  (e₀ : (R ⧸ OrientedTopCohomology.ideal R (Fin.append s t)) ≃ₐ[k] k)

abbrev comparison (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L) :=
  And.intro (Supported.CechHomotopyEquivalence.refinementIso_hom U eF eN l hl (c+m))
    (And.intro (RefinedCoefficientFraction.fraction R P U s t ht
      eP eN eF r δ ev hr w he k hP d hL hzero e₀ y)
      (RefinedScalarFraction.evaluation R P U s t eP k hP d hL hzero e₀ y))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedCoefficientCoordinates
