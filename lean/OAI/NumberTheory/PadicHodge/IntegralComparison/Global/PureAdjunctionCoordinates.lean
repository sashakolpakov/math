import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureIntrinsicCoordinates

/-! # Pure Adjunction Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureAdjunctionCoordinates

noncomputable section

/-! Concentration followed by a genuine survivor morphism agrees in
the original native and additive ordered Čech coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (haU : ∀ i, IsAffineOpen (U i))
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)
  (N : X.Modules) (φ : K.homology c ⟶ N) (q : ℕ)

theorem comparison :
    ((Additive.OrderedCechConcentration.iso U haU K c hK q).hom ≫
      (Additive.OrderedCechConcentration.functor U q).map
        ((single X.Modules (.up ℕ) c).map φ)) ≫
      (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U
        ((single X.Modules (.up ℕ) c).obj N) q).inv =
    (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.iso π U q K).inv ≫
      (PureIntrinsicCoordinates.Intrinsic.concentration π U haU K c hK q).hom ≫
        (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)).map
          (homologyMap ((Cech.ConcentrationNaturality.totalFunctor π U).map
            ((single X.Modules (.up ℕ) c).map φ)) q) := by
  apply (cancel_mono (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U
    ((single X.Modules (.up ℕ) c).obj N) q).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso_naturality π U
    ((single X.Modules (.up ℕ) c).map φ) q]
  have hc := PureIntrinsicCoordinates.Intrinsic.square π U haU K c hK q
  rw [← Category.assoc (PureIntrinsicCoordinates.Intrinsic.concentration π U haU K c hK q).hom,
    hc]
  change _ = (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.iso π U q K).inv ≫
    ((IntrinsicOrdered.CechTransferCoordinates.Intrinsic.iso π U q K).hom ≫
      (Additive.OrderedCechConcentration.iso U haU K c hK q).hom) ≫
    (Additive.OrderedCechConcentration.functor U q).map
      ((single X.Modules (.up ℕ) c).map φ)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureAdjunctionCoordinates
