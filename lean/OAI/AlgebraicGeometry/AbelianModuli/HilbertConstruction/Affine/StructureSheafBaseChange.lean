import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StructureBaseChangeValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.AffineCartesianFunctionTensor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleGlobalSectionsIsomorphism

/-! # Structure Sheaf Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StructureSheafBaseChange

noncomputable section

/-! The actual structure-sheaf base-change morphism is an isomorphism for every Cartesian square of affine schemes. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct
universe u
variable {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine X] [IsAffine Y]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g)

theorem structureBaseChangeMap_appTop_bijective :
    Function.Bijective ((Structure.SheafBaseChange.structureBaseChangeMap H).app ⊤) := by
  let := g.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  let e := GeometricSections.AffineGeometricSections.iso g
    ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X))
  let l := (e.hom ≫ (SectionAdjunction.AffineSectionAdjunction.sections Y).map (Structure.SheafBaseChange.structureBaseChangeMap H)).hom
  have hl : (fun t => l t) = (fun t => AffineCartesianFunctionTensor.CartesianFunctionTensor.map H t) := by
    funext t
    induction t using TensorProduct.inductionOn with
    | tmul r s => exact StructureBaseChangeValues.structureBaseChangeMap_tmul H r s
    | add t t' ht ht' =>
      exact (l.map_add t t').trans
        ((congrArg₂ (fun z w : Γ(P, ⊤) => z + w) ht ht').trans
          ((AffineCartesianFunctionTensor.CartesianFunctionTensor.map H).map_add t t').symm)
  have hbij : Function.Bijective l := by
    change Function.Bijective (fun t => l t)
    rw [hl]
    exact AffineCartesianFunctionTensor.CartesianFunctionTensor.map_bijective H
  exact (Function.Bijective.of_comp_iff ((Structure.SheafBaseChange.structureBaseChangeMap H).app ⊤)
    e.toLinearEquiv.bijective).mp hbij

theorem affineStructureBaseChangeMap_isIso : IsIso (Structure.SheafBaseChange.structureBaseChangeMap H) := by
  have : IsAffine P := .of_isPullback H
  have : ((Scheme.Modules.pullback g).obj
      ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X))).IsQuasicoherent :=
    QuasicoherentPullback.affine_pullback_quasicoherent g _
  apply ModuleGlobalSectionsIsomorphism.affineModule_isIso_of_globalSections_isIso (Structure.SheafBaseChange.structureBaseChangeMap H)
  rw [ConcreteCategory.isIso_iff_bijective]
  exact structureBaseChangeMap_appTop_bijective H

def affineStructureBaseChangeIso :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X)) ≅
      (Scheme.Modules.pushforward b).obj (Line.Bundles.structureModule P) := by
  have := affineStructureBaseChangeMap_isIso H
  exact asIso (Structure.SheafBaseChange.structureBaseChangeMap H)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StructureSheafBaseChange
