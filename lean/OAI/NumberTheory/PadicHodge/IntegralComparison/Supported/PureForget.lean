import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ConcentrationForget

/-! # Pure Forget -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PureForget

noncomputable section

/-! For a complex whose only cohomology is supported on the closed
complement, forgetting support is an isomorphism on the original
cohomology groups. Thus a lift of any original class is unique. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ConcentrationForget
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {R : Type u} [CommRing R] {ι : Type u} [LinearOrder ι] (U : ι → C)
  (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)
  (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index ι q,
    IsZero ((((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) c).obj (K.homology c)).X p).obj
      (op ((AugmentedOrdered.Cech.formal U q).obj a))))

def iso (q : ℕ) := AugmentedCech.Concentration.iso U K c hK q ≪≫
  ConcentrationForget.survivorForgetIso U K c hzero q ≪≫ (ConcentrationForget.ambientIso K c hK q).symm

theorem iso_hom (q : ℕ) : (iso U K c hK hzero q).hom =
    homologyMap (AugmentedOrdered.CechForget.forgetSupport U K) q := by
  apply (cancel_mono (ConcentrationForget.ambientIso K c hK q).hom).mp
  dsimp only [iso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ConcentrationForget.square U K c hK q

include hK hzero in
theorem isIso (q : ℕ) : IsIso (homologyMap (AugmentedOrdered.CechForget.forgetSupport U K) q) := by
  rw [← iso_hom U K c hK hzero q]
  infer_instance

include hK hzero in
theorem unique (q : ℕ) {T : ModuleCat.{u} R}
    (a b : T ⟶ (CechHomotopyEquivalence.functor U q).obj K)
    (h : a ≫ homologyMap (AugmentedOrdered.CechForget.forgetSupport U K) q =
      b ≫ homologyMap (AugmentedOrdered.CechForget.forgetSupport U K) q) : a = b := by
  let := isIso U K c hK hzero q
  exact (cancel_mono _).mp h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PureForget
