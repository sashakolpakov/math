import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.RingSectionBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionAdjunction

/-! # Iso Coefficient Section Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoCoefficientSectionBasis

noncomputable section

/-! Pullback through an isomorphism over the base gives a coefficient-
linear equivalence of actual global sections and transports section bases. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem pullbackSection_bijective_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (M : Y.Modules) :
    Function.Bijective (fun s : Line.Bundles.structureModule Y ⟶ M => Ample.LineBundles.pullbackSection f s) := by
  let F := Scheme.Modules.pullback f
  let : F.IsEquivalence := Affine.SectionAdjunction.AffineSectionAdjunction.pullback_equivalence (asIso f)
  constructor
  · intro s t h
    apply F.map_injective
    exact (cancel_epi (Line.Bundles.structureModulePullbackIso f).inv).mp h
  · intro t
    obtain ⟨s, hs⟩ := F.map_surjective ((Line.Bundles.structureModulePullbackIso f).hom ≫ t)
    refine ⟨s, ?_⟩
    change (Line.Bundles.structureModulePullbackIso f).inv ≫ F.map s = t
    rw [hs, Iso.inv_hom_id_assoc]

variable {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) (M : Y.left.Modules)

local instance sourceHom_isIso : IsIso e.hom.left :=
  inferInstanceAs (IsIso ((Over.forget S).map e.hom))

def sourceIsoCoefficientSectionMap :
    (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor Y.hom.appTop.hom).obj M →ₗ[Γ(S, ⊤)]
      (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor X.hom.appTop.hom).obj ((Scheme.Modules.pullback e.hom.left).obj M) where
  toFun v := Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv X.hom.appTop.hom _
    (Ample.LineBundles.pullbackSection e.hom.left ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv Y.hom.appTop.hom M).symm v))
  map_add' v w := by
    rw [map_add, Section.NonvanishingAddition.pullbackSection_add, map_add]
  map_smul' r v := by
    have hs : (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv Y.hom.appTop.hom M).symm (r • v) =
        Scalar.SectionValues.scalarSection (Y.hom.appTop r) ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv Y.hom.appTop.hom M).symm v) := by
      apply (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv Y.hom.appTop.hom M).injective
      rw [AddEquiv.apply_symm_apply, Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv_scalar, AddEquiv.apply_symm_apply]
    have hw : e.hom.left.appTop (Y.hom.appTop r) = X.hom.appTop r :=
      congrArg (fun a : X.left ⟶ S => a.appTop r) e.hom.w
    change Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv X.hom.appTop.hom _
      (Ample.LineBundles.pullbackSection e.hom.left ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv Y.hom.appTop.hom M).symm (r • v))) = _
    rw [hs, Coefficient.RingSectionBasis.pullbackSection_scalarSection, hw]
    exact Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv_scalar X.hom.appTop.hom _ r _

def sourceIsoCoefficientSectionEquiv :
    (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor Y.hom.appTop.hom).obj M ≃ₗ[Γ(S, ⊤)]
      (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor X.hom.appTop.hom).obj ((Scheme.Modules.pullback e.hom.left).obj M) :=
  LinearEquiv.ofBijective (sourceIsoCoefficientSectionMap e M)
    ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv X.hom.appTop.hom _).bijective.comp
      ((pullbackSection_bijective_of_isIso e.hom.left M).comp
        (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv Y.hom.appTop.hom M).symm.bijective))

theorem coefficientRingBasisFamily_sourceIso {ι : Type v}
    (B : Module.Basis ι Γ(S, ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor Y.hom.appTop.hom).obj M)) (i : ι) :
    Coefficient.RingSectionBasis.coefficientRingBasisFamily X.hom.appTop.hom _ (B.map (sourceIsoCoefficientSectionEquiv e M)) i =
      Ample.LineBundles.pullbackSection e.hom.left (Coefficient.RingSectionBasis.coefficientRingBasisFamily Y.hom.appTop.hom M B i) := by
  apply (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv X.hom.appTop.hom _).injective
  simp only [Coefficient.RingSectionBasis.coefficientRingBasisFamily, Module.Basis.map_apply, AddEquiv.apply_symm_apply]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoCoefficientSectionBasis
