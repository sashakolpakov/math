import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureSectionClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConcentratedCohomology

/-! # Pure Intrinsic Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureIntrinsicCoordinates.Intrinsic

noncomputable section

/-! The globally recovered pure class uses the same scalar-forgotten
native concentration as the projective total trace. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (haU : ∀ i, IsAffineOpen (U i))
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)

def concentration (q : ℕ) :=
  ((((Cech.ConcentrationNaturality.totalFunctor π U).obj K).sc q).mapHomologyIso G) ≪≫
    (G).mapIso (Cech.CohomologyConcentration.homologyIso π U haU K c hK q)

theorem square (q : ℕ) : (concentration π U haU K c hK q).hom ≫
    (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U
      ((single X.Modules (.up ℕ) c).obj (K.homology c)) q).hom =
    (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.iso π U q K).hom ≫
      (Additive.OrderedCechConcentration.iso U haU K c hK q).hom := by
  have h := congrArg
    (((((Cech.ConcentrationNaturality.totalFunctor π U).obj K).sc q).mapHomologyIso G).hom ≫ ·)
      (Additive.OrderedCechConcentration.native_square π U haU K c hK q)
  simpa only [concentration, Iso.trans_hom,
    IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc,
    IntrinsicOrdered.CechTransferCoordinates.Intrinsic.iso, homologyMapIso_hom] using h

theorem section_class (q : ℕ) :
    PureSectionClass.map U haU K c hK q ≫
      (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.iso π U q K).inv ≫
        (concentration π U haU K c hK q).hom =
    PureSectionClass.edge U K c q ≫
      (PureSectionClass.singleIso U (K.homology c) c q).inv ≫
        (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U
          ((single X.Modules (.up ℕ) c).obj (K.homology c)) q).inv := by
  apply (cancel_mono (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U
    ((single X.Modules (.up ℕ) c).obj (K.homology c)) q).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [square π U haU K c hK q, Iso.inv_hom_id_assoc]
  simp only [PureSectionClass.map, PureSectionClass.survivorIso,
    Iso.trans_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureIntrinsicCoordinates.Intrinsic
