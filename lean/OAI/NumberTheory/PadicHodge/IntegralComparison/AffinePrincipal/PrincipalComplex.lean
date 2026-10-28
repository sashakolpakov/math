import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension

/-! # Principal Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.PrincipalComplex

noncomputable section

/-! The principal-open section comparison is an isomorphism of the
actual complexes, natural for their original maps and augmentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (r : Γ(X, U))

local instance chart_sections_additive (W : X.Opens) (hW : IsAffineOpen W) :
    (AffineOpen.InternalHom.sections W hW).Additive where
  map_add := rfl

abbrev tensorFunctor := AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension.functor Γ(X, U) Γ(X, Sections.openSubset U r)

variable {ι : Type v} (c : ComplexShape ι) (K : HomologicalComplex X.Modules c)
  [∀ i, (K.X i).IsQuasicoherent]

def iso :
    ((tensorFunctor U r).mapHomologicalComplex c).obj
        (((Affine.ModuleExactSections.sections U).mapHomologicalComplex c).obj K) ≅
      (((Affine.ModuleExactSections.sections (Sections.openSubset U r)).mapHomologicalComplex c).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (Sections.iso U hU r (K.X i)).toModuleIso)
    (by
      intro i j hij
      apply ConcreteCategory.hom_ext
      intro x
      exact (Sections.naturality U hU r (K.d i j) x).symm)

theorem iso_tmul (i : ι) (a : Γ(X, Sections.openSubset U r)) (m : Γ(K.X i, U)) :
    (iso U hU r c K).hom.f i (a ⊗ₜ[Γ(X, U)] m) =
      a • (K.X i).presheaf.map (Sections.inclusion U r).op m := rfl

variable {K} {L : HomologicalComplex X.Modules c} [∀ i, (L.X i).IsQuasicoherent]

@[reassoc]
theorem naturality (f : K ⟶ L) :
    ((tensorFunctor U r).mapHomologicalComplex c).map
        (((Affine.ModuleExactSections.sections U).mapHomologicalComplex c).map f) ≫
      (iso U hU r c L).hom =
    (iso U hU r c K).hom ≫
      (((Affine.ModuleExactSections.sections (Sections.openSubset U r)).mapHomologicalComplex c).map f) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ConcreteCategory.hom_ext
  intro x
  exact Sections.naturality U hU r (f.f i) x

variable (K)

def chartIso :
    ((tensorFunctor U r).mapHomologicalComplex c).obj
        (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex c).obj K) ≅
      (((AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).mapHomologicalComplex c).obj K) :=
  ((tensorFunctor U r).mapHomologicalComplex c).mapIso
      ((NatIso.mapHomologicalComplex (AffineOpen.LinearHom.sectionsIso U hU) c).app K).symm ≪≫
    iso U hU r c K ≪≫
      (NatIso.mapHomologicalComplex
        (AffineOpen.LinearHom.sectionsIso (Sections.openSubset U r) (hU.basicOpen r)) c).app K

theorem chartIso_tmul (i : ι) (a : Γ(X, Sections.openSubset U r)) (m : Γ(K.X i, U)) :
    (chartIso U hU r c K).hom.f i
        (a ⊗ₜ[Γ(X, U)] (Affine.ChartSections.iso U hU (K.X i)).hom m) =
      (Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) (K.X i)).hom
        (a • (K.X i).presheaf.map (Sections.inclusion U r).op m) := by
  change (Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) (K.X i)).hom
      (Sections.iso U hU r (K.X i)
        (((Affine.ChartSections.iso U hU (K.X i)).inv.hom.baseChange Γ(X, Sections.openSubset U r))
          (a ⊗ₜ[Γ(X, U)] (Affine.ChartSections.iso U hU (K.X i)).hom m))) = _
  rw [LinearMap.baseChange_tmul, Iso.hom_inv_id_apply, Sections.iso_tmul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.PrincipalComplex
