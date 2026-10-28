import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureIntrinsicCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.SurvivorCechEdge

/-! # Pure Section Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureSectionNormalization

noncomputable section

/-! The global pure class has exactly the original degree-zero
Čech augmentation normalization after native concentration. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
  (haU : ∀ i, IsAffineOpen (U i))
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)

def concentration := PureIntrinsicCoordinates.Intrinsic.concentration π U haU K c hK c ≪≫
  (G).mapIso (IntrinsicOrdered.SingleEdge.Intrinsic.columnIso π U (K.homology c) c)

theorem normalization : PureSectionClass.map U haU K c hK c ≫
    (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.iso π U c K).inv ≫
      (concentration π U haU K c hK).hom =
    (Single.SheafGlobalCohomology.iso π U hU (K.homology c) c).hom := by
  have h := congrArg (· ≫ (G).map (IntrinsicOrdered.SingleEdge.Intrinsic.columnIso π U (K.homology c) c).hom)
    (PureIntrinsicCoordinates.Intrinsic.section_class π U haU K c hK c)
  simp only [Category.assoc] at h
  change _ = _ at h
  exact h.trans (Single.SurvivorCechEdge.normalization π U hU (K.homology c) c)

theorem map_eq : PureSectionClass.map U haU K c hK c =
    (Single.SheafGlobalCohomology.iso π U hU (K.homology c) c).hom ≫
      (concentration π U haU K c hK).inv ≫
        (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.iso π U c K).hom := by
  apply (cancel_mono (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.iso π U c K).inv).mp
  apply (cancel_mono (concentration π U haU K c hK).hom).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id]
  exact normalization π U hU haU K c hK

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureSectionNormalization
