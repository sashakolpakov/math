import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality

/-! # Cech Homotopy Equivalence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechHomotopyEquivalence

noncomputable section

/-! Actual HomotopyEquiv maps give explicit inverse maps on the
original supported Čech cohomology, including the normalization of
an augmentation-preserving common-refinement leg. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {R : Type u} [CommRing R] {ι : Type u} [LinearOrder ι] (U : ι → C)

def functor (q : ℕ) : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ ⥤ ModuleCat.{u} R :=
  (AugmentedOrdered.CechFunctor.functor U).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat R) (.up ℕ) (.up ℕ) (.up ℕ) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) q

variable {K L M : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}

theorem homotopy {a b : K ⟶ L} (h : Homotopy a b) (q : ℕ) :
    (functor U q).map a = (functor U q).map b :=
  AugmentedOrdered.CechHomotopy.homology U h q

def iso (e : HomotopyEquiv K L) (q : ℕ) : (functor U q).obj K ≅ (functor U q).obj L where
  hom := (functor U q).map e.hom
  inv := (functor U q).map e.inv
  hom_inv_id := by
    rw [← CategoryTheory.Functor.map_comp, homotopy U e.homotopyHomInvId,
      CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← CategoryTheory.Functor.map_comp, homotopy U e.homotopyInvHomId,
      CategoryTheory.Functor.map_id]

variable (eK : HomotopyEquiv K M) (eL : HomotopyEquiv L M)
  (a : K ⟶ L) (ha : Homotopy (a ≫ eL.hom) eK.hom)

def refinementIso (q : ℕ) : (functor U q).obj K ≅ (functor U q).obj L :=
  iso U eK q ≪≫ (iso U eL q).symm

include ha in
theorem refinementIso_hom (q : ℕ) : (refinementIso U eK eL q).hom = (functor U q).map a := by
  have h := homotopy U ha q
  rw [Functor.map_comp] at h
  apply (cancel_mono (iso U eL q).hom).mp
  change ((iso U eK q).hom ≫ (iso U eL q).inv) ≫ (iso U eL q).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h.symm

@[reassoc]
theorem refinementIso_inv_coordinates (q : ℕ) :
    (refinementIso U eK eL q).inv ≫ (iso U eK q).hom = (iso U eL q).hom := by
  simp [refinementIso, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechHomotopyEquivalence
