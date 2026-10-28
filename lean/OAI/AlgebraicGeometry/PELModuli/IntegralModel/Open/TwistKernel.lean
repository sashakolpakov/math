import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.TwistCoordinates
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FramedRestrictionKernel

/-! # Twist Kernel -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.TwistKernel

noncomputable section

/-! On a chart trivializing a twist, the twisted restriction map vanishes
exactly when the ordinary structure-module map kills the chart coefficient. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite

namespace PolarizationEmbedding

universe u
local instance c44OpenTwistKernelMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

def unitTensorLineIso {X : Scheme.{u}} (L : X.Modules) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⊗ L ≅ L :=
  ((SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl L) ≪≫ λ_ L

def openTwistSourceFrame {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (e : L.restrict U.ι ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    L.restrict U.ι ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme :=
  (Scheme.Modules.restrictFunctor U.ι).mapIso (unitTensorLineIso L).symm ≪≫
    (TwistCoordinates.PolarizationEmbedding.openTwistCoordinate L U e).app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ≪≫ Scheme.Modules.restrictUnitIso U.ι

theorem openTwistSourceFrame_square {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (e : L.restrict U.ι ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    {N : X.Modules} (q : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N) :
    (Scheme.Modules.restrictFunctor U.ι).map (unitTensorLineIso L).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (q ▷ L) ≫
        (TwistCoordinates.PolarizationEmbedding.openTwistCoordinate L U e).hom.app N =
      (openTwistSourceFrame L U e).hom ≫ AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι q := by
  rw [TwistCoordinates.PolarizationEmbedding.openTwistCoordinate_naturality]
  simp only [openTwistSourceFrame, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection, Category.assoc, Iso.hom_inv_id_assoc]
  rfl

theorem openTwist_restriction_zero_iff {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (e : L.restrict U.ι ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    {N : X.Modules} (q : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N) (x : Γ(L.restrict U.ι, ⊤)) :
    ((Scheme.Modules.restrictFunctor U.ι).map (q ▷ L)).app ⊤
      (((Scheme.Modules.restrictFunctor U.ι).map (unitTensorLineIso L).inv).app ⊤ x) = 0 ↔
      (AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι q).app ⊤ (e.hom.app ⊤ x) = 0 := by
  let z := ((Scheme.Modules.restrictFunctor U.ι).map (q ▷ L)).app ⊤
    (((Scheme.Modules.restrictFunctor U.ι).map (unitTensorLineIso L).inv).app ⊤ x)
  let d := (TwistCoordinates.PolarizationEmbedding.openTwistCoordinate L U e).app N
  let v := (SheafOfModules.evaluation (R := U.toScheme.ringCatSheaf) (op ⊤)).mapIso d
  have hz : z = 0 ↔ d.hom.app ⊤ z = 0 := by
    exact v.toLinearEquiv.map_eq_zero_iff.symm
  have he := congrArg (fun a : L.restrict U.ι ⟶ N.restrict U.ι => a.app ⊤ x)
    (openTwistSourceFrame_square L U e q)
  change d.hom.app ⊤ z = (AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι q).app ⊤ ((openTwistSourceFrame L U e).hom.app ⊤ x) at he
  exact hz.trans ((congrArg (fun y => y = 0) he).to_iff.trans
    (FramedRestrictionKernel.PolarizationEmbedding.restriction_kernel_frame_independent (AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι q) (openTwistSourceFrame L U e) e x))

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.TwistKernel
