import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedScalarFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientResidueClass

/-! # Refined Residue Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedResidueClass

noncomputable section

/-! The actual right/inverse-left refinement sends the fixed supported
point class to its coefficient residue, with its canonical scalar intact. -/
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
  (k : Type u) [CommRing k] [Algebra k R]
  (hP : Function.Bijective (algebraMap R (P.obj (op (⊤_ C)))))
  (d : ℕ) (hL : ∀ q, q ≠ d → L.ExactAt q)
  (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q,
    IsZero ((((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) d).obj (L.homology d)).X p).obj
      (op ((AugmentedOrdered.Cech.formal U q).obj a))))
  (e₀ : (R ⧸ OrientedTopCohomology.ideal R (Fin.append s t)) ≃ₐ[k] k)
  (N : Cᵒᵖ ⥤ ModuleCat.{u} R) (α : KoszulPartial.Fractions.modules R P ⟶ N)
  (hN : ∀ (a : Cᵒᵖ) (i : Fin c) (x : N.obj a), s i • x = 0)

def residueClass (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L) :=
  AugmentedOrdered.CechLargeTop.topTotalClass U
    (CoefficientResidueClass.residueTarget R (c := c) N) m (by simp) c
    (CoefficientResidueClass.residueValue R P U t ht N α
      (RefinedScalarFraction.functional R P U s t eP k hP d hL hzero e₀ y))
    (CoefficientResidueClass.residueValue_closed R P U t ht N α _)

include hr in
theorem refined_residue (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L) :
    (Supported.CechHomotopyEquivalence.functor U (c+m)).map (eF.hom ≫ CoefficientResidue.complexMap R P s N α hN)
      (RefinedScalarFraction.refinedMap R P U s eN eF r (c+m) y) =
    residueClass R P U s t ht eP k hP d hL hzero e₀ N α y := by
  rw [Functor.map_comp]
  change (Supported.CechHomotopyEquivalence.functor U (c+m)).map (CoefficientResidue.complexMap R P s N α hN)
      ((Supported.CechHomotopyEquivalence.iso U eF (c+m)).hom
        (RefinedScalarFraction.refinedMap R P U s eN eF r (c+m) y)) = _
  rw [RefinedScalarFraction.fraction R P U s t ht eP eN eF r hr
    k hP d hL hzero e₀ y]
  exact CoefficientResidueClass.supportedClass_residue R P U s t ht N α hN _

variable (l : F ⟶ K) (hl : Homotopy (l ≫ eN.hom) eF.hom)

include hl in
theorem left_isIso (q : ℕ) : IsIso ((Supported.CechHomotopyEquivalence.functor U q).map l) := by
  rw [← Supported.CechHomotopyEquivalence.refinementIso_hom U eF eN l hl q]
  infer_instance

include hr hl in
theorem actual_residue [IsIso ((Supported.CechHomotopyEquivalence.functor U (c+m)).map l)]
    (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L) :
    (Supported.CechHomotopyEquivalence.functor U (c+m)).map (eF.hom ≫ CoefficientResidue.complexMap R P s N α hN)
      (((Supported.CechHomotopyEquivalence.functor U (c+m)).map r ≫ inv ((Supported.CechHomotopyEquivalence.functor U (c+m)).map l)) y) =
    residueClass R P U s t ht eP k hP d hL hzero e₀ N α y := by
  have hi : inv ((Supported.CechHomotopyEquivalence.functor U (c+m)).map l) = (Supported.CechHomotopyEquivalence.refinementIso U eF eN (c+m)).inv := by
    apply (cancel_mono ((Supported.CechHomotopyEquivalence.functor U (c+m)).map l)).mp
    rw [IsIso.inv_hom_id, ← Supported.CechHomotopyEquivalence.refinementIso_hom U eF eN l hl (c+m), Iso.inv_hom_id]
  rw [hi]
  exact refined_residue R P U s t ht eP eN eF r hr k hP d hL hzero e₀ N α hN y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedResidueClass
