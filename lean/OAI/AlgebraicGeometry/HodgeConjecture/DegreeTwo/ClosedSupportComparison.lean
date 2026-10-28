import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportIs

/-! # Closed Support Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportComparison.Constructions

noncomputable section

section

/-! Flasque resolution comparisons preserve exact specified closed supports on actual sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}}
variable {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ} (f : K ⟶ L)

theorem moduleSheafSectionsRestriction_naturality {U W : Opens X} (i : U ⟶ W) :
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections W).mapHomologicalComplex (ComplexShape.up ℕ)).map f ≫
        CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction L i =
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction K i ≫
        ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map f := by
  ext n : 1
  exact ((f.f n).hom.naturality i.op).symm

theorem closedSupportCochainInclusion_naturality (O : Opens X) :
    ((ClosedSupportIs.Constructions.closedSupportSheafFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).map f ≫
        ClosedSupportIs.Constructions.closedSupportCochainInclusion O L = ClosedSupportIs.Constructions.closedSupportCochainInclusion O K ≫ f := by
  ext n : 1
  exact ClosedSupportIs.Constructions.closedSupportSheafMap_inclusion O (f.f n)

variable (O U : Opens X)

def closedSupportSectionKernelMap :
    kernel (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction K (homOfLE (inf_le_left : U ⊓ O ≤ U))) ⟶
      kernel (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction L (homOfLE (inf_le_left : U ⊓ O ≤ U))) :=
  kernel.map _ _
    (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map f)
    (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (U ⊓ O)).mapHomologicalComplex (ComplexShape.up ℕ)).map f)
    (moduleSheafSectionsRestriction_naturality f (homOfLE inf_le_left)).symm

theorem closedSupportSectionKernelMap_inclusion :
    closedSupportSectionKernelMap f O U ≫
        kernel.ι (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction L (homOfLE (inf_le_left : U ⊓ O ≤ U))) =
      kernel.ι (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction K (homOfLE (inf_le_left : U ⊓ O ≤ U))) ≫
        ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map f :=
  kernel.lift_ι _ _ _

theorem closedSupportSectionKernelIso_naturality :
    ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).map f ≫
        (ClosedSupportIs.Constructions.closedSupportSectionKernelIso O U L).hom =
      (ClosedSupportIs.Constructions.closedSupportSectionKernelIso O U K).hom ≫ closedSupportSectionKernelMap f O U := by
  apply (cancel_mono
    (kernel.ι (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction L (homOfLE (inf_le_left : U ⊓ O ≤ U))))).mp
  rw [Category.assoc, ClosedSupportIs.Constructions.closedSupportSectionKernelIso_inclusion, Category.assoc,
    closedSupportSectionKernelMap_inclusion, ← Category.assoc, ClosedSupportIs.Constructions.closedSupportSectionKernelIso_inclusion]
  change ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (((ClosedSupportIs.Constructions.closedSupportSheafFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).map f) ≫
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (ClosedSupportIs.Constructions.closedSupportCochainInclusion O L) = _
  rw [← Functor.map_comp, closedSupportCochainInclusion_naturality, Functor.map_comp]

def closedSupportSectionKernelSequenceMap :
    AlgebraicTopology.Cohomology.Singular.SurjectiveQuasiIso.cochainKernelSequence (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction K (homOfLE (inf_le_left : U ⊓ O ≤ U))) ⟶
      AlgebraicTopology.Cohomology.Singular.SurjectiveQuasiIso.cochainKernelSequence (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction L (homOfLE (inf_le_left : U ⊓ O ≤ U))) where
  τ₁ := closedSupportSectionKernelMap f O U
  τ₂ := ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map f
  τ₃ := ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (U ⊓ O)).mapHomologicalComplex (ComplexShape.up ℕ)).map f
  comm₁₂ := closedSupportSectionKernelMap_inclusion f O U
  comm₂₃ := moduleSheafSectionsRestriction_naturality f
    (homOfLE (inf_le_left : U ⊓ O ≤ U))

theorem flasqueSectionKernelSequence_shortExact
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) :
    (AlgebraicTopology.Cohomology.Singular.SurjectiveQuasiIso.cochainKernelSequence
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction K (homOfLE (inf_le_left : U ⊓ O ≤ U)))).ShortExact := by
  have : Epi (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction K (homOfLE (inf_le_left : U ⊓ O ≤ U))) :=
    HomologicalComplex.epi_of_epi_f _ (fun n => by
      have := hK n
      change Epi ((K.X n).obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op)
      infer_instance)
  change (ShortComplex.mk (kernel.ι _) _ _).ShortExact
  exact { exact := ShortComplex.kernelSequence_exact _ }

theorem closedSupportSectionKernelMap_quasiIso
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) [QuasiIso f] :
    QuasiIso (closedSupportSectionKernelMap f O U) :=
  AlgebraicTopology.Cohomology.Singular.ShortExactQuasiIso.quasiIso_first_of_shortExact (closedSupportSectionKernelSequenceMap f O U)
    (flasqueSectionKernelSequence_shortExact O U K hK)
    (flasqueSectionKernelSequence_shortExact O U L hL)
    (FlasqueResolutionComparison.Constructions.rationalFlasqueSections_quasiIso f hK hL U)
    (FlasqueResolutionComparison.Constructions.rationalFlasqueSections_quasiIso f hK hL (U ⊓ O))

theorem closedSupportFlasqueSections_quasiIso
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) [QuasiIso f] :
    QuasiIso (((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).map f) := by
  have := closedSupportSectionKernelMap_quasiIso f O U hK hL
  have h : QuasiIso
      (((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).map f ≫
        (ClosedSupportIs.Constructions.closedSupportSectionKernelIso O U L).hom) := by
    rw [closedSupportSectionKernelIso_naturality]
    infer_instance
  exact quasiIso_of_comp_right _ (ClosedSupportIs.Constructions.closedSupportSectionKernelIso O U L).hom

end

/-! The native derived section functor with specified closed support is computed by the actual flasque resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (O U : Opens X)
variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (heK : ∀ n, K.ExactAt (n+1))

include hK in
theorem closedSupportResolutionLift_quasiIso :
    QuasiIso (((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (ResolutionHomotopy.Constructions.resolutionLift K heK (FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (K.homology 0)))) := by
  have := ResolutionHomotopy.Constructions.resolutionLift_quasiIso K heK (FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (K.homology 0))
  exact closedSupportFlasqueSections_quasiIso _ O U hK
    (fun n => FlasqueInjectives.Constructions.injectiveModuleSheaf_isFlasque ((FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (K.homology 0)).cocomplex.X n))

def closedSupportResolutionDerivedIso (n : ℕ) :
    (((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n ≅
      ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).rightDerived n).obj (K.homology 0) := by
  have := closedSupportResolutionLift_quasiIso O U K hK heK
  exact isoOfQuasiIsoAt
      (((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (ResolutionHomotopy.Constructions.resolutionLift K heK (FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (K.homology 0)))) n ≪≫
    ((FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (K.homology 0)).isoRightDerivedObj
      (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) n).symm

variable {K} {L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ} (f : K ⟶ L)
variable (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) (heL : ∀ n, L.ExactAt (n+1))

theorem closedSupportResolutionDerivedIso_naturality (n : ℕ) :
    HomologicalComplex.homologyMap
        (((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n ≫
        (closedSupportResolutionDerivedIso O U L hL heL n).hom =
      (closedSupportResolutionDerivedIso O U K hK heK n).hom ≫
        ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).rightDerived n).map (HomologicalComplex.homologyMap f 0) := by
  let I := FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (K.homology 0)
  let J := FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (L.homology 0)
  let F := ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) O U
  let F' := F.mapHomologicalComplex (ComplexShape.up ℕ)
  let d := InjectiveResolution.desc (HomologicalComplex.homologyMap f 0) J I
  have hh : HomologicalComplex.homologyMap (F'.map f) n ≫
      HomologicalComplex.homologyMap (F'.map (ResolutionHomotopy.Constructions.resolutionLift L heL J)) n =
    HomologicalComplex.homologyMap (F'.map (ResolutionHomotopy.Constructions.resolutionLift K heK I)) n ≫
      HomologicalComplex.homologyMap (F'.map d) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp]
    exact (F.mapHomotopy (FlasqueDerivedNaturality.Constructions.resolutionLiftNaturalityHomotopy f heK heL I J)).homologyMap_eq n
  have hn := InjectiveResolution.isoRightDerivedObj_inv_naturality
    (HomologicalComplex.homologyMap f 0) I J d
    (InjectiveResolution.desc_commutes_zero (HomologicalComplex.homologyMap f 0) J I) F n
  change (I.isoRightDerivedObj F n).inv ≫ (F.rightDerived n).map (HomologicalComplex.homologyMap f 0) =
    HomologicalComplex.homologyMap (F'.map d) n ≫ (J.isoRightDerivedObj F n).inv at hn
  change HomologicalComplex.homologyMap (F'.map f) n ≫
      (HomologicalComplex.homologyMap (F'.map (ResolutionHomotopy.Constructions.resolutionLift L heL J)) n ≫
        (J.isoRightDerivedObj F n).inv) =
    (HomologicalComplex.homologyMap (F'.map (ResolutionHomotopy.Constructions.resolutionLift K heK I)) n ≫
      (I.isoRightDerivedObj F n).inv) ≫ (F.rightDerived n).map (HomologicalComplex.homologyMap f 0)
  rw [← Category.assoc, hh, Category.assoc, ← hn, ← Category.assoc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportComparison.Constructions
