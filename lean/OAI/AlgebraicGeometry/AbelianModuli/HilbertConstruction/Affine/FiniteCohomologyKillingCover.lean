import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.LocalCohomologyKilling

/-! # Finite Cohomology Killing Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FiniteCohomologyKillingCover.ZariskiCohomology.LocalKilling

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

theorem zariskiFunctor_map_toAffineCoverModule_eq_zero
    {R : CommRingCat.{u}} {I : Type u} [Finite I]
    {n : ℕ} (M : (Spec R).Modules) (U : I → (Spec R).Opens) (c : Zariski.Cohomology.ZariskiCohomology.H M n)
    (hc : ∀ i, (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) n).map
      ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app M) c = 0) :
    (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) n).map (CohomologyCoverModule.ZariskiCohomology.toAffineCoverModule M U) c = 0 := by
  let : PreservesFiniteProducts (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) n) := by
    let : (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology (Spec R)) n).Additive := by
      infer_instance
    change PreservesFiniteProducts
      (SheafOfModules.toSheaf (Spec R).ringCatSheaf ⋙
        CategoryTheory.Sheaf.functorH
          (Opens.grothendieckTopology (Spec R)) n)
    exact comp_preservesFiniteProducts _ _
  unfold CohomologyCoverModule.ZariskiCohomology.toAffineCoverModule CohomologyCoverModule.ZariskiCohomology.affineCoverModule
  apply Concrete.Pi.map_ext
    (fun i ↦ (Scheme.Modules.restrictFunctor (U i).ι ⋙
      Scheme.Modules.pushforward (U i).ι).obj M)
    (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) n)
  intro i
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    limit.lift_π, Fan.mk_π_app, hc i]
  simp

/-- A positive-degree class is killed on a finite affine cover from the
section-surjectivity data for the preceding injective syzygies. -/
theorem schemeHSucc_finiteAffineKillingCover_of_affine_syzygy_app_surjective
    {R : CommRingCat.{u}} (M : (Spec R).Modules) (n : ℕ)
    (c : Zariski.Cohomology.ZariskiCohomology.H M (n + 1))
    (hsurjective : Open.InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.AffineSyzygyAppSurjective
      ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M) n) :
    ∃ (I : Type u) (U : I → (Spec R).Opens),
      Finite I ∧
      IsOpenCover U ∧
      (∀ i, IsAffine (U i)) ∧
      (∀ i, (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) (n + 1)).map
        ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app M) c = 0) ∧
      (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) (n + 1)).map
        (CohomologyCoverModule.ZariskiCohomology.toAffineCoverModule M U) c = 0 := by
  let F := (SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M
  choose U hUaffine hxU hUkills using fun x : Spec R ↦
    LocalCohomologyKilling.ZariskiCohomology.LocalKilling.exists_affineOpen_H_succ_killing_of_affine_syzygy_app_surjective
      n c hsurjective x
  have hUcover : IsOpenCover U := by
    apply IsOpenCover.mk
    apply le_antisymm le_top
    rw [← SetLike.coe_subset_coe]
    intro x hx
    rw [Opens.coe_iSup]
    exact Set.mem_iUnion.2 ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := hUcover.exists_finite_of_compactSpace
  let V : s → (Spec R).Opens := fun i ↦ U i.1
  have hVkills (i : s) :
      (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) (n + 1)).map
        ((Scheme.Modules.restrictAdjunction (V i).ι).unit.app M) c = 0 := by
    exact Open.AdditiveSheafRestrictionLimits.ZariskiCohomology.LocalKilling.zariskiFunctor_map_restrictAdjunction_unit_eq_zero
      (V i) M c (hUkills i.1)
  let : Finite s := inferInstance
  refine ⟨s, V, inferInstance, hs, fun i ↦ hUaffine i.1,
    hVkills, ?_⟩
  exact zariskiFunctor_map_toAffineCoverModule_eq_zero M V c hVkills

/-- Every degree-one Zariski cohomology class on an affine spectrum is
killed by restriction to the members of a finite affine open cover. The
last conclusion records the same vanishing for the induced map to the
finite product of restriction-pushforwards. -/
theorem schemeHOne_finiteAffineKillingCover
    {R : CommRingCat.{u}} (M : (Spec R).Modules) (c : Zariski.Cohomology.ZariskiCohomology.H M 1) :
    ∃ (I : Type u) (U : I → (Spec R).Opens),
      Finite I ∧
      IsOpenCover U ∧
      (∀ i, IsAffine (U i)) ∧
      (∀ i, (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) 1).map
        ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app M) c = 0) ∧
      (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) 1).map (CohomologyCoverModule.ZariskiCohomology.toAffineCoverModule M U) c = 0 := by
  let F := (SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M
  obtain ⟨q, hq⟩ := Open.RestrictionDegreeOneKilling.ZariskiCohomology.LocalKilling.exists_injectiveCokernel_class (F := F) c
  choose U hUaffine hxU hUkills using fun x : Spec R ↦
    LocalCohomologyKilling.ZariskiCohomology.LocalKilling.exists_affineOpen_HOne_killing c q hq x
  have hUcover : IsOpenCover U := by
    apply IsOpenCover.mk
    apply le_antisymm le_top
    rw [← SetLike.coe_subset_coe]
    intro x hx
    rw [Opens.coe_iSup]
    exact Set.mem_iUnion.2 ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := hUcover.exists_finite_of_compactSpace
  let V : s → (Spec R).Opens := fun i ↦ U i.1
  have hVkills (i : s) :
      (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) 1).map
        ((Scheme.Modules.restrictAdjunction (V i).ι).unit.app M) c = 0 := by
    exact Open.AdditiveSheafRestrictionLimits.ZariskiCohomology.LocalKilling.zariskiFunctor_map_restrictAdjunction_unit_eq_zero
      (V i) M c (hUkills i.1)
  let : Finite s := inferInstance
  refine ⟨s, V, inferInstance, hs, fun i ↦ hUaffine i.1,
    hVkills, ?_⟩
  exact zariskiFunctor_map_toAffineCoverModule_eq_zero M V c hVkills

/-- A degree-two class is killed on a finite affine cover when the
injective-cokernel projection is surjective on the affine basis. This is
the first higher-degree consumer of the cokernel-comparison isomorphism. -/
theorem schemeHTwo_finiteAffineKillingCover_of_affine_cokernel_app_surjective
    {R : CommRingCat.{u}} (M : (Spec R).Modules) (c : Zariski.Cohomology.ZariskiCohomology.H M 2)
    (hsurjective : ∀ (W : (Spec R).Opens), IsAffineOpen W →
      Function.Surjective
        ((cokernel.π (Injective.ι
          ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M))).hom.app
            (op W))) :
    ∃ (I : Type u) (U : I → (Spec R).Opens),
      Finite I ∧
      IsOpenCover U ∧
      (∀ i, IsAffine (U i)) ∧
      (∀ i, (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) 2).map
        ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app M) c = 0) ∧
      (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) 2).map (CohomologyCoverModule.ZariskiCohomology.toAffineCoverModule M U) c = 0 := by
  let F := (SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M
  obtain ⟨q, hq⟩ := Open.RestrictionDegreeOneKilling.ZariskiCohomology.LocalKilling.exists_injectiveCokernel_class (F := F) c
  choose U hUaffine hxU hUkills using fun x : Spec R ↦
    LocalCohomologyKilling.ZariskiCohomology.LocalKilling.exists_affineOpen_HTwo_killing_of_affine_cokernel_app_surjective
      c q hq hsurjective x
  have hUcover : IsOpenCover U := by
    apply IsOpenCover.mk
    apply le_antisymm le_top
    rw [← SetLike.coe_subset_coe]
    intro x hx
    rw [Opens.coe_iSup]
    exact Set.mem_iUnion.2 ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := hUcover.exists_finite_of_compactSpace
  let V : s → (Spec R).Opens := fun i ↦ U i.1
  have hVkills (i : s) :
      (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) 2).map
        ((Scheme.Modules.restrictAdjunction (V i).ι).unit.app M) c = 0 := by
    exact Open.AdditiveSheafRestrictionLimits.ZariskiCohomology.LocalKilling.zariskiFunctor_map_restrictAdjunction_unit_eq_zero
      (V i) M c (hUkills i.1)
  let : Finite s := inferInstance
  refine ⟨s, V, inferInstance, hs, fun i ↦ hUaffine i.1,
    hVkills, ?_⟩
  exact zariskiFunctor_map_toAffineCoverModule_eq_zero M V c hVkills

/-- A degree-three class is killed on a finite affine cover when the first
two injective-cokernel projections are surjective on the affine basis. -/
theorem schemeHThree_finiteAffineKillingCover_of_affine_cokernel_app_surjective
    {R : CommRingCat.{u}} (M : (Spec R).Modules) (c : Zariski.Cohomology.ZariskiCohomology.H M 3)
    (hfirst : ∀ (W : (Spec R).Opens), IsAffineOpen W →
      Function.Surjective
        ((cokernel.π (Injective.ι
          ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M))).hom.app
            (op W)))
    (hsecond : ∀ (W : (Spec R).Opens), IsAffineOpen W →
      Function.Surjective
        ((cokernel.π (Injective.ι (cokernel (Injective.ι
          ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M))))).hom.app
            (op W))) :
    ∃ (I : Type u) (U : I → (Spec R).Opens),
      Finite I ∧
      IsOpenCover U ∧
      (∀ i, IsAffine (U i)) ∧
      (∀ i, (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) 3).map
        ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app M) c = 0) ∧
      (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) 3).map (CohomologyCoverModule.ZariskiCohomology.toAffineCoverModule M U) c = 0 := by
  apply schemeHSucc_finiteAffineKillingCover_of_affine_syzygy_app_surjective
    M 2 c
  exact Open.InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.AffineSyzygyAppSurjective.succ hfirst
    (Open.InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.AffineSyzygyAppSurjective.succ hsecond
      (Open.InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.AffineSyzygyAppSurjective.zero _))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FiniteCohomologyKillingCover.ZariskiCohomology.LocalKilling
