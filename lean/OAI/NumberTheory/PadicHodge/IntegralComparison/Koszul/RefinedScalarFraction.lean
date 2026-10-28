import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.ScalarCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.BasisCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedPointFraction

/-! # Refined Scalar Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedScalarFraction

noncomputable section

/-! The original supported point class, through the actual refinement
zigzag, is the mixed fraction with its canonical base coefficient. -/
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
  (eF : HomotopyEquiv F (KoszulPartial.Components.coefficient R P s)) (r : L ⟶ K)
  (hr : Homotopy (r ≫ eN.hom) (eP.hom ≫ DuplicateFraction.normalMap R s t P))

 def refinedMap (q : ℕ) : (Supported.CechHomotopyEquivalence.functor U q).obj L ⟶ (Supported.CechHomotopyEquivalence.functor U q).obj F :=
  (Supported.CechHomotopyEquivalence.functor U q).map r ≫ (Supported.CechHomotopyEquivalence.refinementIso U eF eN q).inv

 theorem factorization (q : ℕ) :
    RefinedPointFraction.map R P U s t ht eP eN eF r q =
      homologyMap (DualComplexHomology.map R
        (DuplicateFraction.pointIso R s t).hom) q ≫
      homologyMap (KoszulPoint.SupportedTransfer.lift R P U s t ht eP) q ≫
      refinedMap R P U s eN eF r q := by
  dsimp only [RefinedPointFraction.map, KoszulPoint.SupportedTransfer.lift,
    KoszulPoint.SupportedLift.map, refinedMap]
  simp only [homologyMap_comp, Category.assoc]
  rfl

 include hr in
 theorem fraction_of_lift
    (ψ : Module.Dual R (⋀[R]^(c+m) (Fin (c+m) → R)))
    (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L)
    (hy : homologyMap (KoszulPoint.SupportedTransfer.lift R P U s t ht eP) (c+m)
      (TopHomologyCokernel.cycleClass
        (OrientedTopCohomology.dualComplex R (Fin.append s t)) (c+m)
        (OrientedTopCohomology.outgoing_isZero R (Fin.append s t)) ψ) = y) :
    (Supported.CechHomotopyEquivalence.iso U eF (c+m)).hom (refinedMap R P U s eN eF r (c+m) y) =
      KoszulPartial.PartialClass.supportedClass R P U s t ht
        (KoszulPoint.BasisCoordinates.functional R s t ψ) := by
  have h := RefinedPointFraction.class_eq R P U s t ht eP eN eF r hr
    (KoszulPoint.BasisCoordinates.functional R s t ψ)
  have hm := ConcreteCategory.congr_hom (factorization R P U s t ht eP eN eF r (c+m))
    (KoszulPartial.PartialClass.sourceClass R s t (KoszulPoint.BasisCoordinates.functional R s t ψ))
  change RefinedPointFraction.map R P U s t ht eP eN eF r (c+m) _ =
    refinedMap R P U s eN eF r (c+m)
      (homologyMap (KoszulPoint.SupportedTransfer.lift R P U s t ht eP) (c+m)
        (homologyMap (DualComplexHomology.map R
          (DuplicateFraction.pointIso R s t).hom) (c+m) _)) at hm
  rw [KoszulPoint.BasisCoordinates.class_coordinates, hy] at hm
  exact (congrArg (fun z => (Supported.CechHomotopyEquivalence.iso U eF (c+m)).hom z) hm).symm.trans h

 variable (k : Type u) [CommRing k] [Algebra k R]
  (hP : Function.Bijective (algebraMap R (P.obj (op (⊤_ C)))))
  (d : ℕ) (hL : ∀ q, q ≠ d → L.ExactAt q)
  (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q,
    IsZero ((((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) d).obj (L.homology d)).X p).obj
      (op ((AugmentedOrdered.Cech.formal U q).obj a))))
  (e₀ : (R ⧸ OrientedTopCohomology.ideal R (Fin.append s t)) ≃ₐ[k] k)

 def functional (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L) :=
  KoszulPoint.BasisCoordinates.functional R s t
    (KoszulPoint.ScalarCoordinates.representative k R P hP U s t eP d hL hzero e₀ y)

 theorem evaluation (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L) :
    functional R P U s t eP k hP d hL hzero e₀ y
      (TopExteriorCoordinates.generator (KoszulPartial.TopResidue.basis R)) =
    algebraMap k R (KoszulPoint.ScalarCoordinates.scalar k R P hP U s t eP d hL hzero e₀ y) := by
  exact (KoszulPoint.BasisCoordinates.evaluation R s t _).trans
    (KoszulPoint.ScalarCoordinates.evaluation k R P hP U s t eP d hL hzero e₀ y)

 include hr in
 theorem fraction (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L) :
    (Supported.CechHomotopyEquivalence.iso U eF (c+m)).hom (refinedMap R P U s eN eF r (c+m) y) =
      KoszulPartial.PartialClass.supportedClass R P U s t ht
        (functional R P U s t eP k hP d hL hzero e₀ y) :=
  fraction_of_lift R P U s t ht eP eN eF r hr _ y
    (KoszulPoint.ScalarCoordinates.lift_representative k R P hP U s t ht eP d hL hzero e₀ y)

 theorem coefficient (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m) :
    KoszulPartial.Components.coordinateAt R P U t ht (c+m) c m rfl a
      (functional R P U s t eP k hP d hL hzero e₀ y)
      (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c))) =
        KoszulPartial.Fractions.reciprocal R P U t ht a * algebraMap R (P.obj (op ((AugmentedOrdered.Cech.formal U m).obj a)))
          (algebraMap k R
            (KoszulPoint.ScalarCoordinates.scalar k R P hP U s t eP d hL hzero e₀ y)) := by
  rw [KoszulPartial.PartialClass.coefficient, evaluation]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedScalarFraction
