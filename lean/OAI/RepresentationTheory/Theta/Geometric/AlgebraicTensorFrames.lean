import OAI.RepresentationTheory.Theta.Geometric.FrameGlobalIsoRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameRestriction

/-! # Algebraic Tensor Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames

noncomputable section

/-! Product frames for the actual HilbertConstruction tensor sheaf, with exact scalar and
restriction laws. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

open OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameRestriction
universe u

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

def algebraicTensorOpenFrame {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (g : N.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N).restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme :=
  (Scheme.Modules.restrictFunctor U.ι).mapIso (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalTensorObjIso M N).symm ≪≫
    AlgebraicGeometry.SheafCohomology.Projective.TensorSections.restrictMonoidalTensorIso U.ι M N ≪≫ (e ⊗ᵢ g) ≪≫ AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso U.toScheme

theorem algebraicTensorOpenFrame_scalar {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (e e' : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (g g' : N.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (r s : Γ(U.toScheme, ⊤))
    (he : e.hom = e'.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r)
    (hg : g.hom = g'.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection s) :
    (algebraicTensorOpenFrame M N U e g).hom =
      (algebraicTensorOpenFrame M N U e' g').hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (r * s) := by
  simp only [algebraicTensorOpenFrame, Iso.trans_hom, tensorIso_hom, he, hg,
    ← tensorHom_comp_tensorHom, Category.assoc]
  rw [AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso_hom_comp_scalars]

theorem algebraicTensorOpenFrame_restrict {X : Scheme.{u}} (M N : X.Modules)
    {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (g : N.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h (algebraicTensorOpenFrame M N U e g) =
      algebraicTensorOpenFrame M N V (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h e)
        (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h g) := by
  unfold algebraicTensorOpenFrame
  rw [FrameGlobalIsoRestriction.restrictOpenFrame_globalIso, AlgebraicGeometry.SheafCohomology.Projective.TensorFrameRestriction.restrictMonoidalTensorTrivialization_restrictOpen]

end

end OAI.RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames
