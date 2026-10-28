import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.RingSectionBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Section Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.SectionBasis

noncomputable section

/-! A bijective actual section comparison transports a basis to precisely
the pulled-back family of sheaf sections, with the full changed-base scalar action. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (M : X.Modules)

theorem baseChangeGlobalSectionsLinearMap_one_section (s : Line.Bundles.structureModule X ⟶ M) :
    Scalar.SectionBaseChange.baseChangeGlobalSectionsLinearMap H M
        ((1 : Affine.TensorSectionComparison.morphismGlobalAlgebra g) ⊗ₜ[Γ(S, ⊤)] Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv f.appTop.hom M s) =
      Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv b.appTop.hom ((Scheme.Modules.pullback a).obj M)
        (Ample.LineBundles.pullbackSection a s) := by
  change (ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op ⊤)
    ((1 : Affine.TensorSectionComparison.morphismGlobalAlgebra g) ⊗ₜ[Γ(S, ⊤)] Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv f.appTop.hom M s) = _
  erw [ModuleTensorComparison.baseChangeModuleTensorComparison_one]
  exact (Pullback.SectionGlobalValue.pullbackSection_globalValue a s).symm

def cartesianSectionBasis
    (h : Function.Bijective ((ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op ⊤)))
    {ι : Type v} (B : Module.Basis ι Γ(S, ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor f.appTop.hom).obj M)) :
    Module.Basis ι Γ(Y, ⊤)
      ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor b.appTop.hom).obj ((Scheme.Modules.pullback a).obj M)) := by
  let : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  exact (B.baseChange Γ(Y, ⊤)).map
    (LinearEquiv.ofBijective (Scalar.SectionBaseChange.baseChangeGlobalSectionsLinearMap H M) h)

theorem cartesianSectionBasis_family
    (h : Function.Bijective ((ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op ⊤)))
    {ι : Type v} (B : Module.Basis ι Γ(S, ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor f.appTop.hom).obj M))
    (i : ι) :
    Coefficient.RingSectionBasis.coefficientRingBasisFamily b.appTop.hom ((Scheme.Modules.pullback a).obj M)
        (cartesianSectionBasis H M h B) i =
      Ample.LineBundles.pullbackSection a (Coefficient.RingSectionBasis.coefficientRingBasisFamily f.appTop.hom M B i) := by
  apply (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv b.appTop.hom ((Scheme.Modules.pullback a).obj M)).injective
  rw [show Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv b.appTop.hom ((Scheme.Modules.pullback a).obj M)
      (Coefficient.RingSectionBasis.coefficientRingBasisFamily b.appTop.hom ((Scheme.Modules.pullback a).obj M)
        (cartesianSectionBasis H M h B) i) = cartesianSectionBasis H M h B i from
      (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv b.appTop.hom _).apply_symm_apply _]
  let : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  change Scalar.SectionBaseChange.baseChangeGlobalSectionsLinearMap H M ((B.baseChange Γ(Y, ⊤)) i) = _
  rw [Module.Basis.baseChange_apply]
  have he := baseChangeGlobalSectionsLinearMap_one_section H M
    (Coefficient.RingSectionBasis.coefficientRingBasisFamily f.appTop.hom M B i)
  simpa only [Coefficient.RingSectionBasis.coefficientRingBasisFamily, AddEquiv.apply_symm_apply] using he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.SectionBasis
