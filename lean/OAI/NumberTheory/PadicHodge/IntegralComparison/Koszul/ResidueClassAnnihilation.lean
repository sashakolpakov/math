import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedResidueClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SupportedClassAnnihilation

/-! # Residue Class Annihilation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResidueClassAnnihilation

noncomputable section

/-! The literal coefficient residue retains annihilation by the point ideal.
No division by, or normalization of, the fixed point scalar is used. -/
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
  {L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (eP : HomotopyEquiv L (KoszulPartial.Components.coefficient R P (Fin.append s t)))
  (k : Type u) [CommRing k] [Algebra k R]
  (hP : Function.Bijective (algebraMap R (P.obj (op (⊤_ C)))))
  (d : ℕ) (hL : ∀ q, q ≠ d → L.ExactAt q)
  (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q,
    IsZero ((((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) d).obj (L.homology d)).X p).obj
      (op ((AugmentedOrdered.Cech.formal U q).obj a))))
  (e₀ : (R ⧸ OrientedTopCohomology.ideal R (Fin.append s t)) ≃ₐ[k] k)
  (N : Cᵒᵖ ⥤ ModuleCat.{u} R) (α : KoszulPartial.Fractions.modules R P ⟶ N)
  (hN : ∀ (v : Cᵒᵖ) (i : Fin c) (x : N.obj v), s i • x = 0)
  (y : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj L)
  (a : R) (ha : a ∈ OrientedTopCohomology.ideal R (Fin.append s t))

include hN ha in
theorem annihilated : a • RefinedResidueClass.residueClass
    R P U s t ht eP k hP d hL hzero e₀ N α y = 0 := by
  let φ := RefinedScalarFraction.functional R P U s t eP k hP d hL hzero e₀ y
  have h := SupportedClassAnnihilation.map_annihilated R P U s t ht φ a ha
    ((Supported.CechHomotopyEquivalence.functor U (c+m)).map (CoefficientResidue.complexMap R P s N α hN))
  change a • (homologyMap (AugmentedOrdered.CechTopNaturality.totalMap U
    (CoefficientResidue.complexMap R P s N α hN)) (c+m))
      (KoszulPartial.PartialClass.supportedClass R P U s t ht φ) = 0 at h
  rw [CoefficientResidueClass.supportedClass_residue R P U s t ht N α hN φ] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResidueClassAnnihilation
