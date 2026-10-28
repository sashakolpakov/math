import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.LinearHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Homology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologySquare

/-! # Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Cohomology.Comparison

noncomputable section

/-! The original cohomology-sheaf section comparison with the linear
Hom complex respects actual principal-open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.LinearHom

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) [N.IsQuasicoherent] (K : ChainComplex X.Modules ℕ)
  [∀ i, (K.X i).IsQuasicoherent]
  [∀ i, ((Affine.LinearResolutionPurity.internalComplex N K).X i).IsQuasicoherent]

def comparison (i : ℕ) :=
  Affine.LinearResolutionPurity.sectionsHomologyIso U hU N K i ≪≫
    homologyMapIso (Affine.LinearResolutionPurity.sectionComplexIso U hU N K) i

variable (r : Γ(X, U))
  [∀ i, Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i))]
  [∀ i, Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i))]
  (e : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U))

def baseChange (i : ℕ) :
    (PrincipalComplex.tensorFunctor U r).obj
      ((LinearHomBaseChange.homComplex Γ(X, U) (LinearHom.chartComplex U hU K)
        ((AffineOpen.InternalHom.sections U hU).obj N)).homology i) ≅
    (LinearHomBaseChange.homComplex Γ(X, Sections.openSubset U r)
      (LinearHom.chartComplex (Sections.openSubset U r) (hU.basicOpen r) K)
      ((AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj N)).homology i := by
  letI : IsLocalization.Away r Γ(X, Sections.openSubset U r) := hU.isLocalization_basicOpen r
  letI : Module.Flat Γ(X, U) Γ(X, Sections.openSubset U r) :=
    IsLocalization.flat Γ(X, Sections.openSubset U r) (Submonoid.powers r)
  letI (i : ℕ) : Module.Free Γ(X, U) ((LinearHom.chartComplex U hU K).X i) :=
    inferInstanceAs (Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i)))
  letI (i : ℕ) : Module.Finite Γ(X, U) ((LinearHom.chartComplex U hU K).X i) :=
    inferInstanceAs (Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i)))
  exact LinearHomBaseChange.homologyIso Γ(X, U) Γ(X, Sections.openSubset U r)
    (LinearHom.chartComplex U hU K) (LinearHom.chartComplex (Sections.openSubset U r) (hU.basicOpen r) K)
    (PrincipalComplex.chartIso U hU r (.down ℕ) K) _ _ e (LinearHom.targetFrame U hU r N e) i

def sourceBaseChange (i : ℕ) :
    (PrincipalComplex.tensorFunctor U r).obj
      (((((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (.up ℕ)).obj K.op)).homology i) ≅
    (((((AffineOpen.LinearHom.sectionHom (Sections.openSubset U r) N).mapHomologicalComplex (.up ℕ)).obj K.op)).homology i) := by
  letI : IsLocalization.Away r Γ(X, Sections.openSubset U r) := hU.isLocalization_basicOpen r
  letI : Module.Flat Γ(X, U) Γ(X, Sections.openSubset U r) :=
    IsLocalization.flat Γ(X, Sections.openSubset U r) (Submonoid.powers r)
  exact IntegralComparison.Functor.HomologySquare.iso (PrincipalComplex.tensorFunctor U r)
    (PrincipalComplex.iso U hU r (.up ℕ)
      (Affine.LinearResolutionPurity.internalComplex N K)) i

theorem linear_naturality (i : ℕ) :
    (PrincipalComplex.tensorFunctor U r).map
        (homologyMap (Affine.LinearResolutionPurity.sectionComplexIso U hU N K).hom i) ≫
      (baseChange U hU N K r e i).hom =
    (sourceBaseChange U hU N K r i).hom ≫
      homologyMap (Affine.LinearResolutionPurity.sectionComplexIso
        (Sections.openSubset U r) (hU.basicOpen r) N K).hom i := by
  let : IsLocalization.Away r Γ(X, Sections.openSubset U r) := hU.isLocalization_basicOpen r
  let : Module.Flat Γ(X, U) Γ(X, Sections.openSubset U r) :=
    IsLocalization.flat Γ(X, Sections.openSubset U r) (Submonoid.powers r)
  let (i : ℕ) : Module.Free Γ(X, U) ((LinearHom.chartComplex U hU K).X i) :=
    inferInstanceAs (Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i)))
  let (i : ℕ) : Module.Finite Γ(X, U) ((LinearHom.chartComplex U hU K).X i) :=
    inferInstanceAs (Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i)))
  have h := IntegralComparison.Functor.HomologySquare.naturality (PrincipalComplex.tensorFunctor U r)
    (Affine.LinearResolutionPurity.sectionComplexIso U hU N K).hom
    (Affine.LinearResolutionPurity.sectionComplexIso (Sections.openSubset U r) (hU.basicOpen r) N K).hom
    (PrincipalComplex.iso U hU r (.up ℕ)
      (Affine.LinearResolutionPurity.internalComplex N K))
    (LinearHom.linearIso U hU r N K e)
    (LinearHom.sectionComplexIso_square U hU r N K e) i
  have hc := LinearHomBaseChange.homologyIso_canonical Γ(X, U) Γ(X, Sections.openSubset U r)
    (LinearHom.chartComplex U hU K) (LinearHom.chartComplex (Sections.openSubset U r) (hU.basicOpen r) K)
    (PrincipalComplex.chartIso U hU r (.down ℕ) K) _ _ e (LinearHom.targetFrame U hU r N e) i
  change (IntegralComparison.Functor.HomologySquare.iso (PrincipalComplex.tensorFunctor U r)
    (LinearHom.linearIso U hU r N K e) i).hom =
      (baseChange U hU N K r e i).hom at hc
  rw [hc] at h
  exact h

omit [N.IsQuasicoherent] [∀ (i : ℕ), (K.X i).IsQuasicoherent] [∀ (i : ℕ), Module.Free ↑Γ(X, U) ↑((AffineOpen.InternalHom.sections U hU).obj (K.X i))] [∀ (i : ℕ), Module.Finite ↑Γ(X, U) ↑((AffineOpen.InternalHom.sections U hU).obj (K.X i))] in
theorem source_naturality (i : ℕ) :
    (PrincipalComplex.tensorFunctor U r).map
        (Affine.LinearResolutionPurity.sectionsHomologyIso U hU N K i).hom ≫
      (sourceBaseChange U hU N K r i).hom =
    (Homology.restriction U r).app
        ((Affine.LinearResolutionPurity.internalComplex N K).homology i) ≫
      (Affine.LinearResolutionPurity.sectionsHomologyIso
        (Sections.openSubset U r) (hU.basicOpen r) N K i).hom := by
  let : IsLocalization.Away r Γ(X, Sections.openSubset U r) := hU.isLocalization_basicOpen r
  let : Module.Flat Γ(X, U) Γ(X, Sections.openSubset U r) :=
    IsLocalization.flat Γ(X, Sections.openSubset U r) (Submonoid.powers r)
  let L := Affine.LinearResolutionPurity.internalComplex N K
  let : (L.sc i).X₁.IsQuasicoherent := inferInstanceAs
    (((Affine.LinearResolutionPurity.internalComplex N K).X ((ComplexShape.down ℕ).symm.prev i)).IsQuasicoherent)
  let : (L.sc i).X₂.IsQuasicoherent := inferInstanceAs
    (((Affine.LinearResolutionPurity.internalComplex N K).X i).IsQuasicoherent)
  let : (L.sc i).X₃.IsQuasicoherent := inferInstanceAs
    (((Affine.LinearResolutionPurity.internalComplex N K).X ((ComplexShape.down ℕ).symm.next i)).IsQuasicoherent)
  have h := Homology.homology_naturality U r hU (L.sc i)
  have hr := congrArg (fun f => homologyMap f i)
    (Homology.complex_restriction U r hU L)
  change ShortComplex.homologyMap ((L.sc i).mapNatTrans
      (Homology.restriction U r)) =
    homologyMap (PrincipalComplex.iso U hU r (.up ℕ) L).hom i at hr
  rw [hr] at h
  exact h

theorem naturality (i : ℕ) :
    (PrincipalComplex.tensorFunctor U r).map (comparison U hU N K i).hom ≫
        (baseChange U hU N K r e i).hom =
      (Homology.restriction U r).app
        ((Affine.LinearResolutionPurity.internalComplex N K).homology i) ≫
          (comparison (Sections.openSubset U r) (hU.basicOpen r) N K i).hom := by
  dsimp only [comparison, Iso.trans_hom, homologyMapIso_hom]
  rw [Functor.map_comp, Category.assoc, linear_naturality,
    ← Category.assoc, source_naturality, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Cohomology.Comparison
