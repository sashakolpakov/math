import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedOpenScalar
import OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality

/-! # Supported Open Restriction Scalar -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedOpenRestrictionScalar

noncomputable section

/-! The action of a function on a common source open commutes with
restriction between the actual supported principal diagrams. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Injective.Comparison OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SubschemeCoefficientUnit OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedOpenScalar
variable {Y : Scheme.{0}} {C : Type} [Preorder C] [HasFiniteProducts C]
  (F G : C ⥤ Y.Opens) (α : G ⟶ F) {ι : Type} [LinearOrder ι] (W : ι → C)

def restriction (N : Y.Modules) (c q : ℕ) :=
  homologyMap (AffinePrincipal.InjectiveRestriction.sourceMap F G α W N c) q

theorem coefficient_natural {N P : Y.Modules} (a : N ⟶ P) (c q : ℕ) :
    homologyMap (AffinePrincipal.Injective.Comparison.sourceMap F W N c a) q ≫ restriction F G α W P c q =
      restriction F G α W N c q ≫ homologyMap (AffinePrincipal.Injective.Comparison.sourceMap G W N c a) q := by
  have h := congrArg (fun b => homologyMap b q)
    (AffinePrincipal.InjectiveRestriction.naturality F G α W
      ((single _ (.up ℕ) c).map ((SheafOfModules.toSheaf Y.ringCatSheaf).map a)))
  change homologyMap (AffinePrincipal.Injective.Comparison.sourceMap F W N c a ≫
      AffinePrincipal.InjectiveRestriction.sourceMap F G α W P c) q =
    homologyMap (AffinePrincipal.InjectiveRestriction.sourceMap F G α W N c ≫
      AffinePrincipal.Injective.Comparison.sourceMap G W N c a) q at h
  rw [homologyMap_comp, homologyMap_comp] at h
  exact h

variable (V : Y.Opens) (hF : ∀ r, F.obj r ≤ V) (hG : ∀ r, G.obj r ≤ V)
  (N : Y.Modules) (c q : ℕ) (z : Γ(Y,V))

theorem action_restriction :
    SupportedOpenScalar.action F V hF W N c z q ≫ restriction F G α W N c q =
      restriction F G α W N c q ≫ SupportedOpenScalar.action G V hG W N c z q := by
  let eF := SupportedOpenScalar.unitIso F V hF W N c q
  let eG := SupportedOpenScalar.unitIso G V hG W N c q
  let aF := homologyMap (AffinePrincipal.Injective.Comparison.sourceMap F W (Open.SubschemeCoefficientUnit.extension V N) c (Open.SubschemeCoefficientUnit.scalar V N z)) q
  let aG := homologyMap (AffinePrincipal.Injective.Comparison.sourceMap G W (Open.SubschemeCoefficientUnit.extension V N) c (Open.SubschemeCoefficientUnit.scalar V N z)) q
  let rN := restriction F G α W N c q
  let rP := restriction F G α W (Open.SubschemeCoefficientUnit.extension V N) c q
  have hu : eF.hom ≫ rP = rN ≫ eG.hom := coefficient_natural F G α W (Open.SubschemeCoefficientUnit.unit V N) c q
  have hs : aF ≫ rP = rP ≫ aG := coefficient_natural F G α W (Open.SubschemeCoefficientUnit.scalar V N z) c q
  have hi := CohomologyConcentrationNaturality.inverse_square rN rP eF eG hu.symm
  change (eF.hom ≫ aF ≫ eF.inv) ≫ rN = rN ≫ (eG.hom ≫ aG ≫ eG.inv)
  simp only [Category.assoc]
  rw [← hi, ← Category.assoc aF rP, hs]
  simpa only [Category.assoc] using congrArg (fun b => b ≫ aG ≫ eG.inv) hu

theorem fixed_restriction (x : (AffinePrincipal.Injective.Comparison.source F W N c).homology q)
    (hx : SupportedOpenScalar.action F V hF W N c z q x = x) :
    SupportedOpenScalar.action G V hG W N c z q (restriction F G α W N c q x) =
      restriction F G α W N c q x := by
  have h := ConcreteCategory.congr_hom (action_restriction F G α W V hF hG N c q z) x
  change restriction F G α W N c q (SupportedOpenScalar.action F V hF W N c z q x) = _ at h
  rw [hx] at h
  exact h.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedOpenRestrictionScalar
