import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Cokernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Coproducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Kernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionGeneratingSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeFromAffineSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FiniteGeneratingSections
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FormCoherence
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsOpenRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.IntegralSections
import OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeSectionCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ModuleGenerators
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.FiniteTypeIso

/-! # Form Coherence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormCoherence.IntegralFormCoherence

noncomputable section

/-! The native integral zero- and one-form modules on a smooth scheme are coherent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [Smooth X.hom]

abbrev chartRing (U : X.left.affineOpens) : CommAlgCat R :=
  (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op U.val)

abbrev chartModel (U : X.left.affineOpens) : Over (Spec (CommRingCat.of R)) :=
  RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R (chartRing R X U)

local instance chart_open (U : X.left.affineOpens) :
    IsOpenImmersion (X := (chartModel R X U).left) (Y := X.left) U.property.fromSpec :=
  U.property.isOpenImmersion_fromSpec

local instance affine_open (U : X.left.affineOpens) : IsOpenImmersion U.property.fromSpec :=
  U.property.isOpenImmersion_fromSpec

omit [Smooth X.hom] in
theorem chart_over (U : X.left.affineOpens) : U.property.fromSpec ≫ X.hom = (chartModel R X U).hom := by
  rw [RelativeSectionCoefficients.RelativeSpecMaps.structure_eq]
  exact IntegralComparison.AffineOpen.SectionBase.overBase R X U.val U.property

def chartIso (U : X.left.affineOpens) (n : ℕ) :
    FormsModules.IntegralFormsModules.sheaf R (chartModel R X U) n ≅
      (FormsModules.IntegralFormsModules.sheaf R X n).restrict U.property.fromSpec :=
  FormsOpenRestriction.IntegralFormsOpenRestriction.iso (chartModel R X U) X U.property.fromSpec (chart_over R X U) n

omit [Smooth X.hom] in
theorem chart_quasicoherent (U : X.left.affineOpens) (n : ℕ) (hn : n ≤ 1) :
    ((FormsModules.IntegralFormsModules.sheaf R X n).restrict U.property.fromSpec).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent _).prop_of_iso (chartIso R X U n)
    (IntegralAffine.FormCoherence.IntegralAffineFormCoherence.quasicoherent R (chartRing R X U) n hn)

theorem chart_finiteType (U : X.left.affineOpens) (n : ℕ) (hn : n ≤ 1) :
    ((FormsModules.IntegralFormsModules.sheaf R X n).restrict U.property.fromSpec).IsFiniteType := by
  let : Algebra.Smooth R (chartRing R X U) := GeometricComparison.Smooth.IntegralSections.SmoothIntegralSections.algebra_smooth R X U.val U.property
  have hfinite : (FormsModules.IntegralFormsModules.sheaf R (chartModel R X U) n).IsFiniteType :=
    IntegralAffine.FormCoherence.IntegralAffineFormCoherence.finiteType R (chartRing R X U) n hn
  exact @IntegralComparison.Module.FiniteTypeIso.finiteType (chartModel R X U).left _ _ (chartIso R X U n) hfinite

omit [Smooth X.hom] in
theorem cover : (Opens.grothendieckTopology X.left).CoversTop (fun U : X.left.affineOpens => U.val) := by
  rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover, iSup_affineOpens_eq_top X.left]

omit [Smooth X.hom] in
theorem open_quasicoherent (U : X.left.affineOpens) (n : ℕ) (hn : n ≤ 1) :
    ((FormsModules.IntegralFormsModules.sheaf R X n).over U.val).IsQuasicoherent := by
  let : IsAffine U.val.toScheme := U.property
  let := chart_quasicoherent R X U n hn
  let := IntegralComparison.AffineOpen.ModuleGenerators.quasicoherent (FormsModules.IntegralFormsModules.sheaf R X n) U.val U.property
  exact AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceLocality.module_over_quasicoherent_of_affine_restriction (FormsModules.IntegralFormsModules.sheaf R X n) U.val

omit [Smooth X.hom] in
theorem quasicoherent (n : ℕ) (hn : n ≤ 1) : (FormsModules.IntegralFormsModules.sheaf R X n).IsQuasicoherent :=
  @SheafOfModules.IsQuasicoherent.of_coversTop _ _ _ _ _ _ _ _ (FormsModules.IntegralFormsModules.sheaf R X n) _
    (fun U : X.left.affineOpens => U.val) (cover R X) (fun U => open_quasicoherent R X U n hn)

theorem open_generators (U : X.left.affineOpens) (n : ℕ) (hn : n ≤ 1) :
    ∃ G : ((FormsModules.IntegralFormsModules.sheaf R X n).restrict U.val.ι).GeneratingSections, G.IsFiniteType := by
  let := chart_quasicoherent R X U n hn
  let := chart_finiteType R X U n hn
  let M := (FormsModules.IntegralFormsModules.sheaf R X n).restrict U.property.fromSpec
  let : Module.Finite Γ((Spec Γ(X.left, U.val)), ⊤) Γ(M, ⊤) :=
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections.affine_quasicoherent_finiteType_sections_finite M
  obtain ⟨G, hG⟩ := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FiniteGeneratingSections.affine_exists_finite_generatingSections
    ((FormsModules.IntegralFormsModules.sheaf R X n).restrict U.property.fromSpec)
  let : G.IsFiniteType := hG
  exact ⟨IntegralComparison.AffineOpen.ModuleGenerators.generatingSections (FormsModules.IntegralFormsModules.sheaf R X n) U.val U.property G,
    IntegralComparison.AffineOpen.ModuleGenerators.generatingSections_finite (FormsModules.IntegralFormsModules.sheaf R X n) U.val U.property G⟩

theorem finiteType (n : ℕ) (hn : n ≤ 1) : (FormsModules.IntegralFormsModules.sheaf R X n).IsFiniteType := by
  choose G hG using fun U => open_generators R X U n hn
  let q : (FormsModules.IntegralFormsModules.sheaf R X n).LocalGeneratorsData :=
    { I := X.left.affineOpens
      X := fun U => U.val
      coversTop := cover R X
      generators := fun U => AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionGeneratingSections.generatingSectionsOverOfRestrict
        (FormsModules.IntegralFormsModules.sheaf R X n) U.val (G U) }
  have hq : q.IsFiniteType := by
    constructor
    intro U
    let : (G U).IsFiniteType := hG U
    exact AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionGeneratingSections.generatingSectionsOverOfRestrict_isFiniteType
      (FormsModules.IntegralFormsModules.sheaf R X n) U.val (G U)
  exact ⟨⟨q, hq⟩⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormCoherence.IntegralFormCoherence
