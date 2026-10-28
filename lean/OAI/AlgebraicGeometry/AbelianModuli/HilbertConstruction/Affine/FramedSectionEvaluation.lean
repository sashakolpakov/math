import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.FramedSectionEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GeometricMatrixSplitting

/-! # Framed Section Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FramedSectionEvaluation

noncomputable section

/-! An actual frame of a line bundle along a section over Spec R gives
an R-linear evaluation functional, without any field or reducedness
assumption on R. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of R)) (L : Line.Bundles.LineBundle X)
variable (x : Spec (.of R) ⟶ X) (hx : x ≫ p = 𝟙 _)
variable (e : (L.pullback x).sheaf ≅ Line.Bundles.structureModule (Spec (.of R)))

def affineFramedSectionValue (a : Line.Bundles.structureModule X ⟶ L.sheaf) : R :=
  (Scheme.ΓSpecIso (.of R)).hom (Family.FramedSectionEvaluation.familyFramedSectionValue L x e a)

theorem affineFramedSectionValue_add (a b : Line.Bundles.structureModule X ⟶ L.sheaf) :
    affineFramedSectionValue L x e (a + b) =
      affineFramedSectionValue L x e a + affineFramedSectionValue L x e b := by
  simp only [affineFramedSectionValue, Family.FramedSectionEvaluation.familyFramedSectionValue_add, map_add]

include hx in
theorem affineFramedSectionValue_scalar (r : R) (a : Line.Bundles.structureModule X ⟶ L.sheaf) :
    affineFramedSectionValue L x e (Scalar.SectionValues.scalarSection (Coefficient.ModulePresheaf.schemeCoefficientMap p r) a) =
      r * affineFramedSectionValue L x e a := by
  change (Scheme.ΓSpecIso (.of R)).hom
    (Family.FramedSectionEvaluation.familyFramedSectionValue L x e (Scalar.SectionValues.scalarSection (p.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) a)) = _
  rw [Family.FramedSectionEvaluation.familyFramedSectionValue_scalar p L x hx e, map_mul]
  exact congrArg (fun c : R => c * affineFramedSectionValue L x e a)
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of R)).inv_hom_id r)

def affineFramedSectionEvaluation :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf →ₗ[R] R where
  toFun v := affineFramedSectionValue L x e
    ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf).symm v)
  map_add' v w := by
    rw [map_add]
    exact affineFramedSectionValue_add L x e _ _
  map_smul' r v := by
    have he : (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf).symm (r • v) =
        Scalar.SectionValues.scalarSection (Coefficient.ModulePresheaf.schemeCoefficientMap p r)
          ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf).symm v) := by
      apply (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf).injective
      rw [AddEquiv.apply_symm_apply, Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv_scalar,
        AddEquiv.apply_symm_apply]
    rw [he]
    exact affineFramedSectionValue_scalar p L x hx e r _

theorem affineFramedSectionEvaluation_section (a : Line.Bundles.structureModule X ⟶ L.sheaf) :
    affineFramedSectionEvaluation p L x hx e
      (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf a) =
        affineFramedSectionValue L x e a := by
  change affineFramedSectionValue L x e
    ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf).symm
      (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf a)) = _
  rw [AddEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FramedSectionEvaluation
