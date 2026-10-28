import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SectionsLeftExact
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueSectionCokernels
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftFunctor
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomShiftSections

/-! # Flasque Exactness -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.FlasqueExactness

noncomputable section

section

/-! A flasque kernel permits lifting sections while preserving their actual closed support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} (O U : Opens X)
variable (S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X)) (hS : S.ShortExact)
variable [TopCat.Sheaf.IsFlasque S.X₁]

include hS

theorem rationalFlasqueSupportedSequence_epi : Epi ((DerivedComparison.supportedSectionsFunctor O U).map S.g) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro s
  have hU := HodgeConjecture.DegreeTwo.FlasqueSectionCokernels.Constructions.rationalFlasqueSequence_sections_shortExact U S hS
  have hV := HodgeConjecture.DegreeTwo.FlasqueSectionCokernels.Constructions.rationalFlasqueSequence_sections_shortExact (U ⊓ O) S hS
  obtain ⟨b₀, hb⟩ := hU.moduleCat_surjective_g (SectionsLeftExact.supportedSectionsInclusion O U S.X₃ s)
  let b : (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).obj S.X₂ := b₀
  change (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.g b = SectionsLeftExact.supportedSectionsInclusion O U S.X₃ s at hb
  have hz : (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (U ⊓ O)).map S.g
      (S.X₂.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op b) = 0 := by
    have hn := ConcreteCategory.congr_hom
      (S.g.hom.naturality (homOfLE (inf_le_left : U ⊓ O ≤ U)).op) b
    change (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (U ⊓ O)).map S.g
      (S.X₂.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op b) =
      S.X₃.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.g b) at hn
    rw [hb] at hn
    exact hn.trans (SectionsLeftExact.supportedSectionsInclusion_vanishes O U S.X₃ s)
  obtain ⟨a₀, ha₀⟩ := (ShortComplex.moduleCat_exact_iff _).mp hV.exact _ hz
  change (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (U ⊓ O)).map S.f a₀ =
    S.X₂.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op b at ha₀
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective
    (S.X₁.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op)).mp inferInstance a₀
  let b' := b - (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.f a
  have hb' : S.X₂.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op b' = 0 := by
    change S.X₂.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op
      (b - (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.f a) = 0
    rw [map_sub]
    have hn := ConcreteCategory.congr_hom
      (S.f.hom.naturality (homOfLE (inf_le_left : U ⊓ O ≤ U)).op) a
    change (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (U ⊓ O)).map S.f
      (S.X₁.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op a) =
      S.X₂.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.f a) at hn
    rw [ha, ha₀] at hn
    rw [← hn, sub_self]
  have hgb' : (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.g b' = SectionsLeftExact.supportedSectionsInclusion O U S.X₃ s := by
    change (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.g (b - (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.f a) = _
    rw [map_sub]
    have hzero : (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.g ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.f a) = 0 :=
      (S.map (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)).moduleCat_zero_apply a
    rw [hzero, sub_zero]
    exact hb
  obtain ⟨t, ht⟩ := SectionsLeftExact.exists_supportedSection O U S.X₂ b' hb'
  refine ⟨t, ?_⟩
  apply (ModuleCat.mono_iff_injective (SectionsLeftExact.supportedSectionsInclusion O U S.X₃)).mp inferInstance
  have hn := ConcreteCategory.congr_hom (SectionsLeftExact.supportedSectionsInclusion_naturality O U S.g) t
  change SectionsLeftExact.supportedSectionsInclusion O U S.X₃ ((DerivedComparison.supportedSectionsFunctor O U).map S.g t) =
    (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.g (SectionsLeftExact.supportedSectionsInclusion O U S.X₂ t) at hn
  rw [ht] at hn
  exact hn.trans hgb'

theorem rationalFlasqueSupportedSequence_shortExact :
    (S.map (DerivedComparison.supportedSectionsFunctor O U)).ShortExact := by
  have hleft := SectionsLeftExact.supportedSections_shortExact_left O U S hS
  exact ShortComplex.ShortExact.mk' hleft.1 hleft.2 (rationalFlasqueSupportedSequence_epi O U S hS)

end

/-! The genuine supported-section functor preserves the boundary cokernel in the original Thom truncation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} (O U : Opens X)
variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
variable (k : ℕ) (he : ∀ n, n < k → K.ExactAt n)

include hK he

theorem supportedSections_pOpcycles_epi (n : ℕ) (hn : n ≤ k) :
    Epi ((DerivedComparison.supportedSectionsFunctor O U).map (K.pOpcycles n)) := by
  cases n with
  | zero => infer_instance
  | succ n =>
    have := HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.rationalFlasque_opcycles_of_exact_below K hK k he n (Nat.le_of_succ_le hn)
    exact (rationalFlasqueSupportedSequence_shortExact O U (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence K n)
      (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence_shortExact K n (he n (Nat.lt_of_succ_le hn)))).epi_g

theorem supportedSections_preserves_incoming_cokernel (n : ℕ) (hn : n ≤ k) :
    PreservesColimit (parallelPair (K.sc n).f 0) (DerivedComparison.supportedSectionsFunctor O U) := by
  cases n with
  | zero =>
    apply preservesCokernel_zero'
    change K.d ((ComplexShape.up ℕ).prev 0) 0 = 0
    simp
  | succ n =>
    change PreservesColimit (parallelPair (K.d ((ComplexShape.up ℕ).prev (n+1)) (n+1)) 0)
      (DerivedComparison.supportedSectionsFunctor O U)
    rw [CochainComplex.prev_nat_succ]
    have := HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.rationalFlasque_opcycles_of_exact_below K hK k he n (Nat.le_of_succ_le hn)
    have := supportedSections_pOpcycles_epi O U K hK k he n (Nat.le_of_succ_le hn)
    let S := CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence K n
    have hS := rationalFlasqueSupportedSequence_shortExact O U S
      (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence_shortExact K n (he n (Nat.lt_of_succ_le hn)))
    have := hS.epi_g
    refine preservesColimit_of_preserves_colimit_cocone
      (K.opcyclesIsCokernel n (n+1) (by simp)) ?_
    apply (CokernelCofork.isColimitMapCoconeEquiv _ (DerivedComparison.supportedSectionsFunctor O U)).2
    exact isCokernelEpiComp hS.exact.gIsCokernel
      ((DerivedComparison.supportedSectionsFunctor O U).map (K.pOpcycles n)) (by
        change (DerivedComparison.supportedSectionsFunctor O U).map (K.d n (n+1)) =
          (DerivedComparison.supportedSectionsFunctor O U).map (K.pOpcycles n) ≫
            (DerivedComparison.supportedSectionsFunctor O U).map (K.fromOpcycles n (n+1))
        rw [← Functor.map_comp, HomologicalComplex.p_fromOpcycles])

theorem supportedSections_preservesRightHomologyOf (n : ℕ) (hn : n ≤ k) :
    (DerivedComparison.supportedSectionsFunctor O U).PreservesRightHomologyOf (K.sc n) := by
  have := supportedSections_preserves_incoming_cokernel O U K hK k he n hn
  constructor
  intro h
  exact { f := inferInstance, g' := inferInstance }

def supportedGoodShiftFunctorIso :
    (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex (DerivedComparison.supportedSectionsFunctor O U) K).truncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) ≅
      ((DerivedComparison.supportedSectionsFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (K.truncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) :=
  HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.goodShiftFunctorIso (DerivedComparison.supportedSectionsFunctor O U) K k (by
    intro n hn
    have hn0 := HodgeConjecture.DegreeTwo.ThomShiftSections.Constructions.cochainDegreeShift_boundary_eq_zero k n hn
    subst n
    exact supportedSections_preservesRightHomologyOf O U K hK k he k le_rfl)

def supportedGoodShiftCohomologyIso (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O (K.truncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)))).homology n ≅
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K)).homology (k+n) :=
  (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
      (DerivedComparison.supportedSectionsFunctorIso O U (K.truncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k))) ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
      (supportedGoodShiftFunctorIso O U K hK k he).symm ≪≫
    HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex (DerivedComparison.supportedSectionsFunctor O U) K) k n ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) (k+n)).mapIso
      (DerivedComparison.supportedSectionsFunctorIso O U K).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.FlasqueExactness
