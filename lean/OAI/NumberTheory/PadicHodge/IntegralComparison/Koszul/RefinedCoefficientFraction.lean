import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.ScalarCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.BasisCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SupportedCoefficientEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechHomotopyEquivalence

/-! # Refined Coefficient Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedCoefficientFraction

noncomputable section

/-! The actual right/inverse-left common refinement preserves the
weighted fraction formula for arbitrary coefficient resolutions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
open OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechHomotopyEquivalence
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  {L K F T : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (eP : HomotopyEquiv L (KoszulPartial.Components.coefficient R P (Fin.append s t)))
  (eN : HomotopyEquiv K T) (eF : HomotopyEquiv F T) (r : L ⟶ K)
  (δ : KoszulPartial.Components.coefficient R P (Fin.append s t) ⟶ T) (ev : T ⟶ KoszulPartial.Components.coefficient R P s)
  (hr : Homotopy (r ≫ eN.hom) (eP.hom ≫ δ))
  (w : R) (he : Homotopy (δ ≫ ev) (w • DuplicateFraction.normalMap R s t P))

 def coefficientMap := eP.inv ≫ (r ≫ eN.hom)

 def coefficientHomotopy : Homotopy (coefficientMap R P s t eP eN r ≫ ev)
    (w • DuplicateFraction.normalMap R s t P) := by
  have hδ : Homotopy (coefficientMap R P s t eP eN r) δ :=
    (hr.compLeft eP.inv).trans
      ((Homotopy.ofEq (Category.assoc _ _ _).symm).trans (eP.homotopyInvHomId.compRightId δ))
  exact (hδ.compRight ev).trans he

 def refinedMap (q : ℕ) := (Supported.CechHomotopyEquivalence.functor U q).map r ≫ (Supported.CechHomotopyEquivalence.refinementIso U eF eN q).inv

 def evaluatedMap (q : ℕ) := refinedMap R U eN eF r q ≫ (Supported.CechHomotopyEquivalence.iso U eF q).hom ≫ (Supported.CechHomotopyEquivalence.functor U q).map ev

 theorem evaluatedMap_coordinates (q : ℕ) :
    (Supported.CechHomotopyEquivalence.iso U eP q).inv ≫ evaluatedMap R P U s eN eF r ev q =
      (Supported.CechHomotopyEquivalence.functor U q).map (coefficientMap R P s t eP eN r ≫ ev) := by
  dsimp only [evaluatedMap, refinedMap]
  simp only [Category.assoc]
  rw [Supported.CechHomotopyEquivalence.refinementIso_inv_coordinates_assoc]
  change (Supported.CechHomotopyEquivalence.functor U q).map eP.inv ≫ (Supported.CechHomotopyEquivalence.functor U q).map r ≫
    (Supported.CechHomotopyEquivalence.functor U q).map eN.hom ≫ (Supported.CechHomotopyEquivalence.functor U q).map ev = _
  simp only [coefficientMap, Functor.map_comp, Category.assoc]

 theorem supported_factorization (q : ℕ) :
    homologyMap (SupportedCoefficientEvaluation.supported R P U s t ht
      (coefficientMap R P s t eP eN r) ev) q =
    homologyMap (DualComplexHomology.map R (DuplicateFraction.pointIso R s t).hom) q ≫
      homologyMap (KoszulPoint.SupportedTransfer.lift R P U s t ht eP) q ≫
        evaluatedMap R P U s eN eF r ev q := by
  dsimp only [SupportedCoefficientEvaluation.supported,
    KoszulPoint.SupportedTransfer.lift, KoszulPoint.SupportedLift.map]
  simp only [homologyMap_comp, Category.assoc]
  change _ = _ ≫ _ ≫ ((Supported.CechHomotopyEquivalence.iso U eP q).inv ≫ evaluatedMap R P U s eN eF r ev q)
  rw [evaluatedMap_coordinates, Functor.map_comp]
  rfl

 include hr he in
 theorem fraction_of_lift
    (ψ : Module.Dual R (⋀[R]^(c+m) (Fin (c+m) → R)))
    (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L)
    (hy : homologyMap (KoszulPoint.SupportedTransfer.lift R P U s t ht eP) (c+m)
      (TopHomologyCokernel.cycleClass
        (OrientedTopCohomology.dualComplex R (Fin.append s t)) (c+m)
        (OrientedTopCohomology.outgoing_isZero R (Fin.append s t)) ψ) = y) :
    evaluatedMap R P U s eN eF r ev (c+m) y =
      w • KoszulPartial.PartialClass.supportedClass R P U s t ht
        (KoszulPoint.BasisCoordinates.functional R s t ψ) := by
  have h := SupportedCoefficientEvaluation.class_eq R P U s t ht
    (coefficientMap R P s t eP eN r) ev w
    (coefficientHomotopy R P s t eP eN r δ ev hr w he)
    (KoszulPoint.BasisCoordinates.functional R s t ψ)
  have hm := ConcreteCategory.congr_hom (supported_factorization R P U s t ht eP eN eF r ev (c+m))
    (KoszulPartial.PartialClass.sourceClass R s t (KoszulPoint.BasisCoordinates.functional R s t ψ))
  change _ = evaluatedMap R P U s eN eF r ev (c+m)
    (homologyMap (KoszulPoint.SupportedTransfer.lift R P U s t ht eP) (c+m)
      (homologyMap (DualComplexHomology.map R
        (DuplicateFraction.pointIso R s t).hom) (c+m) _)) at hm
  rw [KoszulPoint.BasisCoordinates.class_coordinates, hy] at hm
  exact hm.symm.trans h

 variable (k : Type u) [CommRing k] [Algebra k R]
  (hP : Function.Bijective (algebraMap R (P.obj (op (⊤_ C)))))
  (d : ℕ) (hL : ∀ q, q ≠ d → L.ExactAt q)
  (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q,
    IsZero ((((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) d).obj (L.homology d)).X p).obj
      (op ((AugmentedOrdered.Cech.formal U q).obj a))))
  (e₀ : (R ⧸ OrientedTopCohomology.ideal R (Fin.append s t)) ≃ₐ[k] k)

abbrev fraction (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L) :=
  fraction_of_lift R P U s t ht eP eN eF r δ ev hr w he
    (KoszulPoint.ScalarCoordinates.representative k R P hP U s t eP d hL hzero e₀ y) y
    (KoszulPoint.ScalarCoordinates.lift_representative k R P hP U s t ht eP d hL hzero e₀ y)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedCoefficientFraction
