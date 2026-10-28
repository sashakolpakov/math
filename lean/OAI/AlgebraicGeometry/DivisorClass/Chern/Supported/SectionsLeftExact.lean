import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.DerivedComparison

/-! # Sections Left Exact -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SectionsLeftExact

noncomputable section

/-! The actual supported-section functor preserves kernels and finite limits. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} (O U : Opens X)

def supportedSectionsInclusion (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) :
    (DerivedComparison.supportedSectionsFunctor O U).obj F ⟶ (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).obj F :=
  (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O F).hom.app (op U)

theorem supportedSectionsInclusion_naturality
    {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (f : F ⟶ G) :
    (DerivedComparison.supportedSectionsFunctor O U).map f ≫ supportedSectionsInclusion O U G =
      supportedSectionsInclusion O U F ≫ (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map f :=
  congrArg (fun g => g.hom.app (op U)) (ClosedSupportFunctor.closedSupportSheafMap_inclusion O f)

instance supportedSectionsInclusion_mono (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) :
    Mono (supportedSectionsInclusion O U F) :=
  inferInstanceAs (Mono ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O F)))

theorem supportedSectionsInclusion_vanishes (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X)
    (s : (DerivedComparison.supportedSectionsFunctor O U).obj F) :
    F.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op (supportedSectionsInclusion O U F s) = 0 :=
  CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_vanishes O U F s

theorem exists_supportedSection (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X)
    (s : (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).obj F)
    (hs : F.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op s = 0) :
    ∃ t : (DerivedComparison.supportedSectionsFunctor O U).obj F, supportedSectionsInclusion O U F t = s := by
  have h : s ∈ LinearMap.ker (F.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op).hom := hs
  rw [← CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_range O U F] at h
  exact h

theorem supportedSectionsMap_mono {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    (f : F ⟶ G) [Mono f] : Mono ((DerivedComparison.supportedSectionsFunctor O U).map f) := by
  have : Mono ((DerivedComparison.supportedSectionsFunctor O U).map f ≫ supportedSectionsInclusion O U G) := by
    rw [supportedSectionsInclusion_naturality]
    infer_instance
  exact mono_of_mono ((DerivedComparison.supportedSectionsFunctor O U).map f) (supportedSectionsInclusion O U G)

theorem supportedSections_shortExact_left
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X)) (hS : S.ShortExact) :
    (S.map (DerivedComparison.supportedSectionsFunctor O U)).Exact ∧ Mono ((DerivedComparison.supportedSectionsFunctor O U).map S.f) := by
  have := hS.mono_f
  refine ⟨?_, supportedSectionsMap_mono O U S.f⟩
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro b hb
  change (DerivedComparison.supportedSectionsFunctor O U).map S.g b = 0 at hb
  have hg : (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.g (supportedSectionsInclusion O U S.X₂ b) = 0 := by
    have h := ConcreteCategory.congr_hom (supportedSectionsInclusion_naturality O U S.g) b
    change supportedSectionsInclusion O U S.X₃ ((DerivedComparison.supportedSectionsFunctor O U).map S.g b) = _ at h
    rw [hb, map_zero] at h
    exact h.symm
  have hp := ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U)).mp inferInstance S hS).1
  obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp hp _ hg
  change (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.f a = supportedSectionsInclusion O U S.X₂ b at ha
  have hz : S.X₁.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op a = 0 := by
    apply (ModuleCat.mono_iff_injective
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (U ⊓ O)).map S.f)).mp inferInstance
    rw [map_zero]
    have hn := ConcreteCategory.congr_hom
      (S.f.hom.naturality (homOfLE (inf_le_left : U ⊓ O ≤ U)).op) a
    change (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (U ⊓ O)).map S.f
      (S.X₁.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op a) =
      S.X₂.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.f a) at hn
    rw [ha] at hn
    exact hn.trans (supportedSectionsInclusion_vanishes O U S.X₂ b)
  obtain ⟨s, hs⟩ := exists_supportedSection O U S.X₁ a hz
  refine ⟨s, ?_⟩
  apply (ModuleCat.mono_iff_injective (supportedSectionsInclusion O U S.X₂)).mp inferInstance
  have hn := ConcreteCategory.congr_hom (supportedSectionsInclusion_naturality O U S.f) s
  change supportedSectionsInclusion O U S.X₂ ((DerivedComparison.supportedSectionsFunctor O U).map S.f s) =
    (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.f (supportedSectionsInclusion O U S.X₁ s) at hn
  rw [hs] at hn
  exact hn.trans ha

instance supportedSectionsFunctor_preservesFiniteLimits : PreservesFiniteLimits (DerivedComparison.supportedSectionsFunctor O U) :=
  (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono (DerivedComparison.supportedSectionsFunctor O U)).mpr
    (supportedSections_shortExact_left O U)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SectionsLeftExact
