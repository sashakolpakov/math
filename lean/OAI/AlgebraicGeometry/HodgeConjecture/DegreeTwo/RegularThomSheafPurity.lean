import OAI.AlgebraicGeometry.CycleClass.Geometric.RegularThom

/-! # Regular Thom Sheaf Purity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularThomSheafPurity.Constructions

noncomputable section

/-! The genuine regular-locus supported sheaf complex has cohomology in exactly its Thom degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

theorem regularThomStalk_isZero_except (y : Z.regularAmbientSpace) (n : ℕ) (hn : n ≠ 2*p) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex Z.regularThomSheafComplex y).homology n) := by
  by_cases hy : y ∈ Set.range Z.regularComplementInclusion
  · obtain ⟨x,rfl⟩ := hy
    apply (Z.regularFixedNormalPair x).supportedStalk_homology_isZero
      Z.regularThomComplementOpen rfl n
    simpa only [Module.finrank_fin_fun] using hn
  · exact CycleClass.Geometric.SupportStalkVanishes.Cycles.supportedSingularSheaf_stalk_homology_isZero_of_mem
      (X := TopCat.of Z.regularAmbientSpace) (ModuleCat.of ℚ ℚ)
      Z.regularThomComplementOpen y hy n

theorem regularThomSheaf_homology_isZero_except (n : ℕ) (hn : n ≠ 2*p) :
    IsZero (Z.regularThomSheafComplex.homology n) :=
  CycleClass.Geometric.GlobalSupportPurity.Cycles.rationalSheafComplex_homology_isZero_of_stalk Z.regularThomSheafComplex n
    (fun y => regularThomStalk_isZero_except Z y n hn)

theorem regularThomSheaf_exactAt_except (n : ℕ) (hn : n ≠ 2*p) :
    Z.regularThomSheafComplex.ExactAt n :=
  CycleClass.Geometric.GlobalSupportPurity.Cycles.rationalSheafComplex_exactAt_of_stalk_isZero Z.regularThomSheafComplex n
    (fun y => regularThomStalk_isZero_except Z y n hn)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularThomSheafPurity.Constructions
