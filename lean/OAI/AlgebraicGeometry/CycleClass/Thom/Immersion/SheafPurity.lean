import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion

/-! # Sheaf Purity -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Immersion.SheafPurity.Constructions.Construction

/-! The genuine regular-locus supported sheaf complex has cohomology in exactly its Thom degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)

theorem regularThomStalk_isZero_except (y : Z.regularAmbientSpace) (n : ℕ) (hn : n ≠ 2*p) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex Z.regularThomSheafComplex y).homology n) := by
  by_cases hy : y ∈ Set.range Z.regularComplementInclusion
  · obtain ⟨x,rfl⟩ := hy
    apply (Z.regularFixedNormalPair x).supportedStalk_homology_isZero
      Z.regularThomComplementOpen rfl n
    simpa only [Module.finrank_fin_fun] using hn
  · exact Geometric.SupportStalkVanishes.Cycles.supportedSingularSheaf_stalk_homology_isZero_of_mem
      (X := TopCat.of Z.regularAmbientSpace) (ModuleCat.of ℚ ℚ)
      Z.regularThomComplementOpen y hy n

theorem regularThomSheaf_homology_isZero_except (n : ℕ) (hn : n ≠ 2*p) :
    IsZero (Z.regularThomSheafComplex.homology n) :=
  Geometric.GlobalSupportPurity.Cycles.rationalSheafComplex_homology_isZero_of_stalk Z.regularThomSheafComplex n
    (fun y => regularThomStalk_isZero_except Z y n hn)

theorem regularThomSheaf_exactAt_except (n : ℕ) (hn : n ≠ 2*p) :
    Z.regularThomSheafComplex.ExactAt n :=
  Geometric.GlobalSupportPurity.Cycles.rationalSheafComplex_exactAt_of_stalk_isZero Z.regularThomSheafComplex n
    (fun y => regularThomStalk_isZero_except Z y n hn)

end AlgebraicGeometry.CycleClass.Thom.Immersion.SheafPurity.Constructions.Construction

namespace AlgebraicGeometry.CycleClass.Thom.Immersion.SheafPurity.Constructions.SupportDetection

/-! A supported class in the Thom degree is determined on arbitrary
open neighborhoods covering the actual embedded source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SheafPurity.Constructions.Construction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)

theorem relativeClass_eq_of_neighborhoods
    (U : Z.regularAnalyticSpace → Opens V.analyticSpace)
    (hU : ∀ z, Z.regularComplementInclusion z ∈ U z)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      (Set.range Z.regularComplementInclusion)ᶜ (2 * p))
    (hab : ∀ z, Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) V.analyticSpace
      (Set.range Z.regularComplementInclusion)ᶜ (U z) (2 * p) a =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) V.analyticSpace
        (Set.range Z.regularComplementInclusion)ᶜ (U z) (2 * p) b) : a = b := by
  let O := Z.regularThomComplementOpen
  let S := (Z.regularThomSheafComplex.homology (2 * p)).obj
  have hi : IsIso (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) V.analyticSpace O (2 * p)) :=
    Geometric.ComplexThom.Cycles.relativeCohomologyGlobalSectionMap_isIso V.analyticSpace O (2 * p)
      (fun y n hn => Construction.regularThomStalk_isZero_except Z y n (ne_of_lt hn))
  apply (ModuleCat.mono_iff_injective
    (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) V.analyticSpace O (2 * p))).mp inferInstance
  apply Geometric.SupportedGerms.Cycles.supportedCohomologySection_ext_on_support (ModuleCat.of ℚ ℚ) V.analyticSpace O ⊤ (2 * p)
  intro y _ hy
  have hyr : y ∈ Set.range Z.regularComplementInclusion := not_not.mp hy
  obtain ⟨z, rfl⟩ := hyr
  have image (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace (O : Set V.analyticSpace) (2 * p)) :
      S.map (homOfLE (le_top : U z ≤ ⊤)).op
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) V.analyticSpace O (2 * p) c) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) V.analyticSpace O (U z) (2 * p)
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) V.analyticSpace (O : Set V.analyticSpace) (U z) (2 * p) c) :=
    ConcreteCategory.congr_hom
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap_restrict (ModuleCat.of ℚ ℚ) V.analyticSpace O (U z) (2 * p)) c
  have he : S.map (homOfLE (le_top : U z ≤ ⊤)).op
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) V.analyticSpace O (2 * p) a) =
    S.map (homOfLE (le_top : U z ≤ ⊤)).op
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) V.analyticSpace O (2 * p) b) := by
    rw [image a, image b]
    exact congrArg (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) V.analyticSpace O (U z) (2 * p)) (hab z)
  have hg := congrArg (TopCat.Presheaf.germ S (U z) (Z.regularComplementInclusion z) (hU z)) he
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hg
  exact hg

end AlgebraicGeometry.CycleClass.Thom.Immersion.SheafPurity.Constructions.SupportDetection

end

end OAI
