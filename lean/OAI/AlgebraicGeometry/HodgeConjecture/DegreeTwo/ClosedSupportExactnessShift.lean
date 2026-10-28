import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportIs
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftRepresentatives

/-! # Closed Support Exactness Shift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift.Constructions

noncomputable section

section

/-! Sections with specified closed support are left exact and preserve sequences with flasque kernel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X : TopCat.{0}} (O U : Opens X)

abbrev closedSectionInclusion (F : TopCat.Sheaf (ModuleCat.{0} R) X) :=
  (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O F)

theorem closedSectionInclusion_naturality {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (f : F ⟶ G) :
    (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map f ≫ closedSectionInclusion O U G =
      closedSectionInclusion O U F ≫ (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map f := by
  change (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map (ClosedSupportIs.Constructions.closedSupportSheafMap O f) ≫
      (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O G) = _
  rw [← Functor.map_comp, ClosedSupportIs.Constructions.closedSupportSheafMap_inclusion, Functor.map_comp]

theorem closedSupportSection_map_mono {F G : TopCat.Sheaf (ModuleCat.{0} R) X}
    (f : F ⟶ G) [Mono f] : Mono ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map f) := by
  have h : Mono (closedSectionInclusion O U F ≫ (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map f) := inferInstance
  rw [← closedSectionInclusion_naturality O U f] at h
  exact mono_of_mono ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map f) (closedSectionInclusion O U G)

theorem closedSupportSection_map_exact
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X)) (hS : S.ShortExact) :
    (S.map (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U)).Exact := by
  have := hS.mono_f
  have hU := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)).mp inferInstance S hS
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have hx' : (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.g (closedSectionInclusion O U S.X₂ x) = 0 := by
    have h := ConcreteCategory.congr_hom (closedSectionInclusion_naturality O U S.g) x
    change closedSectionInclusion O U S.X₃ ((S.map (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U)).g x) = _ at h
    rw [hx, map_zero] at h
    exact h.symm
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hU.1 _ hx'
  have hyzero : S.X₁.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op y = 0 := by
    apply (ModuleCat.mono_iff_injective ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (U ⊓ O)).map S.f)).mp inferInstance
    rw [map_zero]
    have h := ConcreteCategory.congr_hom
      (S.f.hom.naturality (homOfLE (inf_le_left : U ⊓ O ≤ U)).op) y
    change (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (U ⊓ O)).map S.f
      (S.X₁.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op y) =
      S.X₂.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op
        ((S.map (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)).f y) at h
    rw [hy] at h
    exact h.trans (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_vanishes O U S.X₂ x)
  have hymem : y ∈ LinearMap.range (closedSectionInclusion O U S.X₁).hom := by
    change y ∈ LinearMap.range (((CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O S.X₁).hom.app (op U)).hom)
    rw [CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_range]
    exact hyzero
  obtain ⟨z, hz⟩ := hymem
  refine ⟨z, ?_⟩
  apply CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_injective O U S.X₂
  have h := ConcreteCategory.congr_hom (closedSectionInclusion_naturality O U S.f) z
  change closedSectionInclusion O U S.X₂ ((S.map (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U)).f z) =
    (S.map (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)).f (closedSectionInclusion O U S.X₁ z) at h
  rw [hz, hy] at h
  exact h

instance closedSupportSectionFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := R) O U) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr
  intro S hS
  have := hS.mono_f
  exact ⟨closedSupportSection_map_exact O U S hS, closedSupportSection_map_mono O U S.f⟩

end

section

/-! A flasque kernel lets a section lift while retaining its specified support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (O U : Opens X)

variable (S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X)) (hS : S.ShortExact)
variable [TopCat.Sheaf.IsFlasque S.X₁]

include hS

theorem closedSupportFlasqueSection_map_epi : Epi ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map S.g) := by
  have hU := FlasqueSectionCokernels.Constructions.rationalFlasqueSequence_sections_shortExact U S hS
  have hW := FlasqueSectionCokernels.Constructions.rationalFlasqueSequence_sections_shortExact (U ⊓ O) S hS
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro x
  obtain ⟨y, hy⟩ := hU.moduleCat_surjective_g (closedSectionInclusion O U S.X₃ x)
  have hyzero : (S.map (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (U ⊓ O))).g
      (S.X₂.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op y) = 0 := by
    have h := ConcreteCategory.congr_hom
      (S.g.hom.naturality (homOfLE (inf_le_left : U ⊓ O ≤ U)).op) y
    change (S.map (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (U ⊓ O))).g
      (S.X₂.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op y) =
      S.X₃.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op
        ((S.map (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)).g y) at h
    rw [hy] at h
    exact h.trans (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_vanishes O U S.X₃ x)
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp hW.exact _ hyzero
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective
    (S.X₁.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op)).mp inferInstance z
  let t := y - (S.map (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)).f w
  have htzero : S.X₂.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op t = 0 := by
    have h := ConcreteCategory.congr_hom
      (S.f.hom.naturality (homOfLE (inf_le_left : U ⊓ O ≤ U)).op) w
    change (S.map (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (U ⊓ O))).f
      (S.X₁.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op w) =
      S.X₂.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op
        ((S.map (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)).f w) at h
    rw [hw, hz] at h
    dsimp only [t]
    rw [map_sub, ← h, sub_self]
  have htmem : t ∈ LinearMap.range (((CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O S.X₂).hom.app (op U)).hom) := by
    rw [CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_range]
    exact htzero
  obtain ⟨v, hv⟩ := htmem
  change closedSectionInclusion O U S.X₂ v = t at hv
  refine ⟨v, ?_⟩
  apply CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_injective O U S.X₃
  have h := ConcreteCategory.congr_hom (closedSectionInclusion_naturality O U S.g) v
  change closedSectionInclusion O U S.X₃ ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map S.g v) =
    (S.map (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)).g (closedSectionInclusion O U S.X₂ v) at h
  rw [hv] at h
  dsimp only [t] at h
  rw [map_sub, (S.map (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)).moduleCat_zero_apply, sub_zero, hy] at h
  exact h

theorem closedSupportFlasqueSection_shortExact :
    (S.map (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U)).ShortExact := by
  have := hS.mono_f
  exact ShortComplex.ShortExact.mk'
    (closedSupportSection_map_exact O U S hS)
    (closedSupportSection_map_mono O U S.f)
    (closedSupportFlasqueSection_map_epi O U S hS)

end

section

/-! Specified support preserves the boundary cokernels of a flasque resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (O : Opens X)

variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
variable (k : ℕ) (he : ∀ n, n<k → K.ExactAt n)

include hK he

theorem closedSupportFlasqueSections_pOpcycles_epi (U : Opens X) (n : ℕ) (hn : n≤k) :
    Epi ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map (K.pOpcycles n)) := by
  cases n with
  | zero => infer_instance
  | succ n =>
    have := ThomGoodShiftFlasque.Constructions.rationalFlasque_opcycles_of_exact_below K hK k he n (Nat.le_of_succ_le hn)
    exact (closedSupportFlasqueSection_shortExact O U (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence K n)
      (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence_shortExact K n (he n (Nat.lt_of_succ_le hn)))).epi_g

theorem closedSupportFlasqueSections_preserves_incoming_cokernel (U : Opens X) (n : ℕ) (hn : n≤k) :
    PreservesColimit (parallelPair (K.sc n).f 0) (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) := by
  cases n with
  | zero =>
    apply preservesCokernel_zero'
    change K.d ((ComplexShape.up ℕ).prev 0) 0 = 0
    simp
  | succ n =>
    change PreservesColimit (parallelPair (K.d ((ComplexShape.up ℕ).prev (n+1)) (n+1)) 0)
      (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U)
    rw [CochainComplex.prev_nat_succ]
    have := ThomGoodShiftFlasque.Constructions.rationalFlasque_opcycles_of_exact_below K hK k he n (Nat.le_of_succ_le hn)
    have := closedSupportFlasqueSections_pOpcycles_epi O K hK k he U n (Nat.le_of_succ_le hn)
    let S := CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence K n
    have hS := closedSupportFlasqueSection_shortExact O U S
      (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence_shortExact K n (he n (Nat.lt_of_succ_le hn)))
    have := hS.epi_g
    refine preservesColimit_of_preserves_colimit_cocone
      (K.opcyclesIsCokernel n (n+1) (by simp)) ?_
    apply (CokernelCofork.isColimitMapCoconeEquiv _ (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U)).2
    exact isCokernelEpiComp hS.exact.gIsCokernel
      ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map (K.pOpcycles n)) (by
        change (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map (K.d n (n+1)) =
          (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map (K.pOpcycles n) ≫
            (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map (K.fromOpcycles n (n+1))
        rw [← Functor.map_comp, HomologicalComplex.p_fromOpcycles])

theorem closedSupportFlasqueSections_preservesRightHomologyOf (U : Opens X) (n : ℕ) (hn : n≤k) :
    (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).PreservesRightHomologyOf (K.sc n) := by
  have := closedSupportFlasqueSections_preserves_incoming_cokernel O K hK k he U n hn
  constructor
  intro h
  exact { f := inferInstance, g' := inferInstance }

def closedSupportFlasqueSections_opcyclesIso (U : Opens X) (n : ℕ) (hn : n≤k) :
    (GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K).opcycles n ≅ (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).obj (K.opcycles n) := by
  have := closedSupportFlasqueSections_preservesRightHomologyOf O K hK k he U n hn
  exact (K.sc n).mapOpcyclesIso (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U)

end

section

/-! The actual degree shift commutes with sections of a specified closed support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (O U : Opens X)
variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
variable (k : ℕ) (he : ∀ n, n<k → K.ExactAt n)

def closedSupportGoodShiftIso :
    (GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K).truncGE'
        (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) ≅
      GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U)
        (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) :=
  GoodShiftFunctor.Constructions.goodShiftFunctorIso (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K k (by
    intro n hn
    have hn0 := ThomShiftSections.Constructions.cochainDegreeShift_boundary_eq_zero k n hn
    subst n
    exact closedSupportFlasqueSections_preservesRightHomologyOf O K hK k he U k le_rfl)

def closedSupportGoodShiftCohomologyIso (n : ℕ) :
    (GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U)
      (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k))).homology n ≅
    (GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K).homology (k+n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n).mapIso
      (closedSupportGoodShiftIso O U K hK k he).symm ≪≫
    GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K) k n

end

/-! The supported shift comparison carries each original cocycle class through unchanged. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (O U : Opens X)
variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (k : ℕ) (he : ∀ n, n<k → K.ExactAt n)

theorem closedSupportGoodShiftIso_projection :
    (GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K).restrictionToTruncGE'
        (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) ≫ (closedSupportGoodShiftIso O U K hK k he).hom =
      ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) :=
  GoodShiftComparison.Constructions.goodShiftFunctorIso_projection (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K k _

theorem closedSupportGoodShiftCohomologyIso_class (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K) (k+n)) :
    (closedSupportGoodShiftCohomologyIso O U K hK k he n).hom
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (closedSupportGoodShiftIso O U K hK k he).hom n
        (GoodShiftRepresentatives.Constructions.cochainGoodShiftCocycle (GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K) k n c))) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (k+n) c := by
  change (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K) k n).hom
      (HomologicalComplex.homologyMap (closedSupportGoodShiftIso O U K hK k he).inv n
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (closedSupportGoodShiftIso O U K hK k he).hom n
          (GoodShiftRepresentatives.Constructions.cochainGoodShiftCocycle (GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K) k n c)))) = _
  have hi := ConcreteCategory.congr_hom
    (((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n).mapIso
      (closedSupportGoodShiftIso O U K hK k he)).hom_inv_id)
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n (GoodShiftRepresentatives.Constructions.cochainGoodShiftCocycle
      (GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K) k n c))
  change HomologicalComplex.homologyMap (closedSupportGoodShiftIso O U K hK k he).inv n
    (HomologicalComplex.homologyMap (closedSupportGoodShiftIso O U K hK k he).hom n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n (GoodShiftRepresentatives.Constructions.cochainGoodShiftCocycle
        (GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K) k n c))) =
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n (GoodShiftRepresentatives.Constructions.cochainGoodShiftCocycle
      (GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K) k n c) at hi
  rw [← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, hi, GoodShiftRepresentatives.Constructions.cochainGoodShiftHomologyIso_class]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift.Constructions
