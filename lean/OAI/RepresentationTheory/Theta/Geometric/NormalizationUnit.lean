import OAI.RepresentationTheory.Theta.Geometric.ModelAxisNormalization
import OAI.RepresentationTheory.Theta.Geometric.MinimalSections
import OAI.RepresentationTheory.Theta.Geometric.MinimalFieldExtensionRanks
import OAI.RepresentationTheory.Theta.Geometric.Local.NormalizationUnit
import OAI.RepresentationTheory.Theta.Geometric.TrivialFamilySectionRank
import OAI.RepresentationTheory.Theta.Geometric.Normalized.ClosedFiberFrames
import OAI.RepresentationTheory.Theta.Geometric.SectionAxisBaseChange
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.Normalization

/-! # Normalization Unit -/

namespace OAI.RepresentationTheory.Theta.Geometric.NormalizationUnit

noncomputable section

/-! A trivial geometric fiber supplies both the rank-one first module
and the unit normalization coefficient of the original local Cech model. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.Normalization.Construction

universe u

theorem trivialization_exists_normalizedSection {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (ρ : Y ⟶ T) (b : T ⟶ Y) (hb : b ≫ ρ = 𝟙 T)
    (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : (Scheme.Modules.pullback f).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    ∃ a : (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op ⊤),
      (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r).hom.app ⊤
        (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback b ((Scheme.Modules.pullback f).obj M) a) = (1 : Γ(T, ⊤)) := by
  let v := AlgebraicGeometry.FormalGeometry.Completion.Frame.Normalization.Construction.normalizedFrame f ρ b g s h M r e.symm
  refine ⟨AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _ v.hom, ?_⟩
  rw [← Normalized.ClosedFiberFrames.rigidifiedSection_endValue]
  change SectionAxisBaseChange.sectionAxisScalar f b g s h M r v.hom = 1
  exact (SectionAxisBaseChange.sectionAxisScalar_frame f b g s h M r v).trans
    (AlgebraicGeometry.FormalGeometry.Completion.Frame.Normalization.Construction.normalizedFrame_scalar f ρ b hb g s h M r e.symm)

variable {X Y S T : Scheme.{u}} [IsLocalRing Γ(S, ⊤)]
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (π : X ⟶ S) (ρ : Y ⟶ T) (hπ : f ≫ π = ρ ≫ g)
    (hs : s ≫ π = 𝟙 S) (hb : b ≫ ρ = 𝟙 T)
    (M : X.Modules) {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S) (i : I)
    (hi : (⊤ : S.Opens) ≤ s ⁻¹ᵁ AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0
      (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i))
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U) (hU : iSup U = ⊤)
    [hmodel : QuasiIsoAt (AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g hπ M U φ) 0]
    (P : AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2))

include h hb hπ hU hmodel in
theorem modelNormalization_unit_of_trivial_fiber
    [IsLocalHom g.appTop.hom]
    (e : Γ(S, ⊤) ≃ₗ[Γ(S, ⊤)] P.complex.X₁)
    (eM : (Scheme.Modules.pullback f).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    IsUnit (MinimalNormalizedSections.minimalSectionFunctional P (ModelAxisNormalization.modelAxisFunctional s π hs M U r i hi φ) (e 1)) := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  apply Local.NormalizationUnit.minimalSectionFunctional_isUnit_of_local_extension P Γ(T, ⊤) e
  obtain ⟨a, ha⟩ := trivialization_exists_normalizedSection f ρ b hb g s h M r eM
  obtain ⟨z, rfl⟩ := (AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections f π ρ g hπ M U hU φ).surjective a
  refine ⟨z.val, z.property, ?_⟩
  exact (ModelAxisNormalization.modelAxisNormalization_value f b g s h π ρ hπ hs hb M U r i hi φ hU z).symm.trans ha

include hπ hU hmodel in
theorem minimal_first_finrank_of_trivial_geometric_fiber
    (hT : IsField Γ(T, ⊤)) [IsLocalHom g.appTop.hom] [IsIso ρ.appTop]
    (eM : (Scheme.Modules.pullback f).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    Module.finrank Γ(S, ⊤) P.complex.X₁ = 1 := by
  let : Field Γ(T, ⊤) := hT.toField
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let E := (MinimalSections.scalarFirstCyclesLinearEquiv g.appTop.hom C).symm.trans
    (AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections f π ρ g hπ M U hU φ)
  exact (MinimalFieldExtensionRanks.minimal_first_finrank_eq_field_cycles P Γ(T, ⊤)).trans
    (E.finrank_eq.trans (TrivialFamilySectionRank.trivialBaseSections_finrank ρ eM))

end

end OAI.RepresentationTheory.Theta.Geometric.NormalizationUnit
