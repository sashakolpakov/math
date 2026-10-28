import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionSpanning
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionFrameCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleTensorScalarAction

/-! # Section Tensor Scalar Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionTensorScalarMap

noncomputable section

/-! The actual coefficient section tensor pairing is linear over the
new ring and sends a scalar times a section to that scalar times the
actual pulled-back section. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
variable {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (a : Y ⟶ X) (c : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Y, ⊤))
variable (hq : q.comp (algebraMap R B) = a.appTop.hom.comp c)

def coefficientSectionTensorScalarMap :
    (B ⊗[R] (GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M) →ₗ[B]
      (GlobalSectionsFunctor.coefficientGlobalSectionsFunctor q).obj ((Scheme.Modules.pullback a).obj M) where
  toFun z := Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq ⊤ z
  map_add' x y := (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq ⊤).map_add x y
  map_smul' b z := CompatibleTensorScalarAction.compatibleScalarTensorMap_left_action
    (Section.PresheafExtendedScalars.pushedCoefficientScalarComponent a c ((Scheme.Modules.pullback a).obj M) q ⊤)
    (Section.PresheafExtendedScalars.pushedCoefficientScalarComponent_coefficient a c ((Scheme.Modules.pullback a).obj M) q hq ⊤)
    ((PullbackSectionMap.coefficientPullbackSectionPresheafMap a c M).app (op ⊤)).hom b z

theorem coefficientSectionTensorScalarMap_section (b : B) (s : Line.Bundles.structureModule X ⟶ M) :
    coefficientSectionTensorScalarMap a c M q hq
      (b ⊗ₜ[R] RingSectionBasis.coefficientRingSectionAddEquiv c M s) =
      b • RingSectionBasis.coefficientRingSectionAddEquiv q ((Scheme.Modules.pullback a).obj M) (Ample.LineBundles.pullbackSection a s) := by
  have hx : (Global.Sections.moduleSectionHomEquiv M).symm
      (show Γ(M, ⊤) from RingSectionBasis.coefficientRingSectionAddEquiv c M s) = s :=
    (Global.Sections.moduleSectionHomEquiv M).symm_apply_apply s
  have h := SectionSpanning.coefficientTensorComparison_scalarSectionValue a c M q hq b
    (RingSectionBasis.coefficientRingSectionAddEquiv c M s)
  rw [hx] at h
  exact h.trans (RingSectionBasis.coefficientRingSectionAddEquiv_scalar q ((Scheme.Modules.pullback a).obj M)
    b (Ample.LineBundles.pullbackSection a s))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionTensorScalarMap
