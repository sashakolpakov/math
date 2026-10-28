import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedCoefficientFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedResidueClass

/-! # Refined Coefficient Residue Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedCoefficientResidueClass

noncomputable section

/-! Evaluating the original finite-coefficient point transfer and then
taking its normal residue retains the same scalar point residue. -/
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
  (eN : HomotopyEquiv K T) (eF : HomotopyEquiv F T) (r : L ⟶ K)
  (δ : KoszulPartial.Components.coefficient R P (Fin.append s t) ⟶ T) (ev : T ⟶ KoszulPartial.Components.coefficient R P s)
  (hr : Homotopy (r ≫ eN.hom) (eP.hom ≫ δ))
  (w : R) (he : Homotopy (δ ≫ ev) (w • DuplicateFraction.normalMap R s t P))
  (k : Type u) [CommRing k] [Algebra k R]
  (hP : Function.Bijective (algebraMap R (P.obj (op (⊤_ C)))))
  (d : ℕ) (hL : ∀ q, q ≠ d → L.ExactAt q)
  (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q,
    IsZero ((((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) d).obj (L.homology d)).X p).obj
      (op ((AugmentedOrdered.Cech.formal U q).obj a))))
  (e₀ : (R ⧸ OrientedTopCohomology.ideal R (Fin.append s t)) ≃ₐ[k] k)
  (N : Cᵒᵖ ⥤ ModuleCat.{u} R) (α : KoszulPartial.Fractions.modules R P ⟶ N)
  (hN : ∀ (a : Cᵒᵖ) (i : Fin c) (x : N.obj a), s i • x = 0)

include hr he in
theorem refined_residue (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L) :
    (Supported.CechHomotopyEquivalence.functor U (c+m)).map
        (eF.hom ≫ ev ≫ CoefficientResidue.complexMap R P s N α hN)
      (RefinedCoefficientFraction.refinedMap R U eN eF r (c+m) y) =
    w • RefinedResidueClass.residueClass R P U s t ht eP
      k hP d hL hzero e₀ N α y := by
  have h := RefinedCoefficientFraction.fraction R P U s t ht
    eP eN eF r δ ev hr w he k hP d hL hzero e₀ y
  have h' := congrArg
    ((Supported.CechHomotopyEquivalence.functor U (c+m)).map (CoefficientResidue.complexMap R P s N α hN)) h
  rw [((Supported.CechHomotopyEquivalence.functor U (c+m)).map
      (CoefficientResidue.complexMap R P s N α hN)).hom.map_smul] at h'
  have hres : (Supported.CechHomotopyEquivalence.functor U (c+m)).map
      (CoefficientResidue.complexMap R P s N α hN)
      (KoszulPartial.PartialClass.supportedClass R P U s t ht
        (RefinedScalarFraction.functional R P U s t eP k hP d hL hzero e₀ y)) =
      RefinedResidueClass.residueClass R P U s t ht eP k hP d hL hzero e₀ N α y :=
    CoefficientResidueClass.supportedClass_residue R P U s t ht N α hN _
  have h'' := h'.trans (congrArg (fun z => w • z) hres)
  simpa only [Functor.map_comp, ConcreteCategory.comp_apply,
    RefinedCoefficientFraction.evaluatedMap,
    Supported.CechHomotopyEquivalence.iso] using h''

variable (l : F ⟶ K) (hl : Homotopy (l ≫ eN.hom) eF.hom)

include hr he hl in
theorem actual_residue [IsIso ((Supported.CechHomotopyEquivalence.functor U (c+m)).map l)]
    (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L) :
    (Supported.CechHomotopyEquivalence.functor U (c+m)).map
        (eF.hom ≫ ev ≫ CoefficientResidue.complexMap R P s N α hN)
      (((Supported.CechHomotopyEquivalence.functor U (c+m)).map r ≫ inv ((Supported.CechHomotopyEquivalence.functor U (c+m)).map l)) y) =
    w • RefinedResidueClass.residueClass R P U s t ht eP
      k hP d hL hzero e₀ N α y := by
  have hi : inv ((Supported.CechHomotopyEquivalence.functor U (c+m)).map l) = (Supported.CechHomotopyEquivalence.refinementIso U eF eN (c+m)).inv := by
    apply (cancel_mono ((Supported.CechHomotopyEquivalence.functor U (c+m)).map l)).mp
    rw [IsIso.inv_hom_id, ← Supported.CechHomotopyEquivalence.refinementIso_hom U eF eN l hl (c+m), Iso.inv_hom_id]
  rw [hi]
  exact refined_residue R P U s t ht eP eN eF r δ ev hr w he
    k hP d hL hzero e₀ N α hN y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedCoefficientResidueClass
