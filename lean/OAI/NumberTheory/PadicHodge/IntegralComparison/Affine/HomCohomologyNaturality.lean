import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Cohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalDualInvariance

/-! # Hom Cohomology Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomCohomologyNaturality

noncomputable section

/-! The actual affine internal-Hom cohomology comparison is natural
for every chain map, before making choices of resolution lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) [N.IsQuasicoherent]
  (K L : ChainComplex X.Modules ℕ)
  [∀ i, (K.X i).IsQuasicoherent] [∀ i, (L.X i).IsQuasicoherent]
  [∀ i, ((LinearResolutionPurity.internalComplex N K).X i).IsQuasicoherent]
  [∀ i, ((LinearResolutionPurity.internalComplex N L).X i).IsQuasicoherent]
  (a : K ⟶ L)

abbrev nativeMap := (LocalDualInvariance.functor N).map a.op
abbrev chartMap := ((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).map a
abbrev linearMap := (ProjectiveResolution.HomNaturality.functor
  ((linearYoneda Γ(X, U) (ModuleCat Γ(X, U))).obj ((AffineOpen.InternalHom.sections U hU).obj N))).map
    (chartMap U hU K L a).op

omit [N.IsQuasicoherent] [∀ (i : ℕ), ((LinearResolutionPurity.internalComplex N K).X i).IsQuasicoherent] [∀ (i : ℕ), ((LinearResolutionPurity.internalComplex N L).X i).IsQuasicoherent] in
theorem section_square :
    ((ModuleExactSections.sections U).mapHomologicalComplex (.up ℕ)).map (nativeMap N K L a) ≫
        (LinearResolutionPurity.sectionComplexIso U hU N K).hom =
      (LinearResolutionPurity.sectionComplexIso U hU N L).hom ≫ linearMap U hU N K L a := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact (AffineOpen.LinearHom.comparison U hU N).naturality (a.f q).op

omit [N.IsQuasicoherent] [∀ (i : ℕ), (K.X i).IsQuasicoherent] [∀ (i : ℕ), (L.X i).IsQuasicoherent] in
theorem sections_naturality (q : ℕ) :
    (ModuleExactSections.sections U).map (homologyMap (nativeMap N K L a) q) ≫
      (LinearResolutionPurity.sectionsHomologyIso U hU N K q).hom =
    (LinearResolutionPurity.sectionsHomologyIso U hU N L q).hom ≫
      homologyMap (((ModuleExactSections.sections U).mapHomologicalComplex (.up ℕ)).map
        (nativeMap N K L a)) q := by
  let F := ModuleExactSections.sections U
  let DK := LinearResolutionPurity.internalComplex N K
  let DL := LinearResolutionPurity.internalComplex N L
  let : (DK.sc q).X₁.IsQuasicoherent := inferInstanceAs (DK.X ((ComplexShape.up ℕ).prev q)).IsQuasicoherent
  let : (DK.sc q).X₂.IsQuasicoherent := inferInstanceAs (DK.X q).IsQuasicoherent
  let : (DK.sc q).X₃.IsQuasicoherent := inferInstanceAs (DK.X ((ComplexShape.up ℕ).next q)).IsQuasicoherent
  let : (DL.sc q).X₁.IsQuasicoherent := inferInstanceAs (DL.X ((ComplexShape.up ℕ).prev q)).IsQuasicoherent
  let : (DL.sc q).X₂.IsQuasicoherent := inferInstanceAs (DL.X q).IsQuasicoherent
  let : (DL.sc q).X₃.IsQuasicoherent := inferInstanceAs (DL.X ((ComplexShape.up ℕ).next q)).IsQuasicoherent
  let : F.PreservesLeftHomologyOf (DK.sc q) := ModuleHomology.preservesLeft U hU _
  let : F.PreservesLeftHomologyOf (DL.sc q) := ModuleHomology.preservesLeft U hU _
  let a' : DL ⟶ DK := nativeMap N K L a
  exact ShortComplex.mapHomologyIso_inv_naturality
    (show DL.sc q ⟶ DK.sc q from (shortComplexFunctor X.Modules (.up ℕ) q).map a') F

omit [N.IsQuasicoherent] in
theorem naturality (q : ℕ) :
    (ModuleExactSections.sections U).map (homologyMap (nativeMap N K L a) q) ≫
      (AffinePrincipal.Cohomology.Comparison.comparison U hU N K q).hom =
    (AffinePrincipal.Cohomology.Comparison.comparison U hU N L q).hom ≫
      homologyMap (linearMap U hU N K L a) q := by
  have h₁ := sections_naturality U hU N K L a q
  have h₂ := congrArg (fun t => homologyMap t q) (section_square U hU N K L a)
  simp only [homologyMap_comp] at h₂
  exact DualComplexHomology.compose_squares _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomCohomologyNaturality
