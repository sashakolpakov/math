import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompositeFieldHomFaithfulness

/-! # Action Field Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ActionFieldFaithfulness

noncomputable section

/-! Equality of actual integral actions is detected on one field-valued
fibre of a connected family pulled back through a field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionScheme

universe u

theorem integralAction_eq_of_field_restriction
    {S : Scheme.{u}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    {R K F : Type u} [CommRing R] [Field K] [Field F]
    (k : Spec (.of K) ⟶ S) (T : Over (Spec (.of K)))
    [PreconnectedSpace T.left] (s : Spec (.of F) ⟶ T.left)
    (ρ σ : ActionData.IntegralAction R (A.pullback (T.hom ≫ k)))
    (h : PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A ρ
        (Over.homMk s rfl : Over.mk (s ≫ (T.hom ≫ k)) ⟶ Over.mk (T.hom ≫ k)) =
      PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A σ
        (Over.homMk s rfl : Over.mk (s ≫ (T.hom ≫ k)) ⟶ Over.mk (T.hom ≫ k))) :
    ρ = σ := by
  let V : Over S := Over.mk (T.hom ≫ k)
  let W : Over S := Over.mk (s ≫ V.hom)
  let c : W ⟶ V := Over.homMk s rfl
  apply PELModuli.IntegralModel.Finite.Actions.integralAction_ext
  intro r
  apply A.compositePullback_hom_eq_of_field_fiber A k T.hom s
  have he := congrArg
    (fun τ : ActionData.IntegralAction R (A.pullback W.hom) => τ.map r) h
  change (PELModuli.IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A c).inv ≫
      (Over.pullback s).map (ρ.map r) ≫
        (PELModuli.IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A c).hom =
    (PELModuli.IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A c).inv ≫
      (Over.pullback s).map (σ.map r) ≫
        (PELModuli.IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A c).hom at he
  exact (cancel_mono (PELModuli.IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A c).hom).mp
    ((cancel_epi (PELModuli.IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A c).inv).mp
      (by simpa only [Category.assoc] using! he))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ActionFieldFaithfulness
