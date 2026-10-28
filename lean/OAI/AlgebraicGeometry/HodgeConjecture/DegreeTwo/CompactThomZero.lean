import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GlobalSourceThomNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularCompactThomStage

/-! # Compact Thom Zero -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomZero.Constructions

noncomputable section

section

/-! The actual compact source stages of the Thom isomorphism form a compatible directed system. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem relativeComplementChange_cast_naturality (X : TopCat.{0})
    {A B A' B' : Set X} (h : A ⊆ B) (h' : A' ⊆ B') (eA : A = A') (eB : B = B') (n : ℕ) :
    HomologicalComplex.homologyMap (RelativeTopSupportNaturality.Constructions.relativeComplementChange X h) n ≫
        (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) eA)).hom =
      (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) eB)).hom ≫
        HomologicalComplex.homologyMap (RelativeTopSupportNaturality.Constructions.relativeComplementChange X h') n := by
  subst A'
  subst B'
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

theorem regularCompactImageComplement_antitone {K L : Compacts Z.regularAnalyticSpace} (h : K ≤ L) :
    RegularCompactThomStage.Constructions.regularCompactImageComplement Z L ≤ RegularCompactThomStage.Constructions.regularCompactImageComplement Z K :=
  Set.compl_subset_compl.mpr (OpenEmbeddingExtension.Constructions.embeddingCompactImage_mono (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) h)

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceCompactThomStageIso_naturality
    {K L : Compacts Z.regularAnalyticSpace} (h : K ≤ L) (n : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) h n ≫ (RegularCompactThomStage.Constructions.regularSourceCompactThomStageIso Z a ha L n).hom =
      (RegularCompactThomStage.Constructions.regularSourceCompactThomStageIso Z a ha K n).hom ≫
        AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ)
          (OpenEmbeddingExtension.Constructions.embeddingCompactImage_mono (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) h) (2+n) := by
  let hO := regularCompactImageComplement_antitone Z h
  exact SupportedSourceThomNaturality.Constructions.sourceTargetIso_naturality
    (eqToIso (congrArg (fun B => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAnalyticSpace) B n) (RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage Z K)))
    (eqToIso (congrArg (fun B => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAnalyticSpace) B n) (RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage Z L)))
    (GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha (RegularCompactThomStage.Constructions.regularCompactImageComplement Z K) n)
    (GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha (RegularCompactThomStage.Constructions.regularCompactImageComplement Z L) n)
    (eqToIso (congrArg (fun B => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) B (2+n)) (RegularCompactThomStage.Constructions.regularCompactThom_unionComplement Z K)))
    (eqToIso (congrArg (fun B => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) B (2+n)) (RegularCompactThomStage.Constructions.regularCompactThom_unionComplement Z L))) _ _ _ _
    (relativeComplementChange_cast_naturality (TopCat.of Z.regularAnalyticSpace)
      (show ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj (RegularCompactThomStage.Constructions.regularCompactImageComplement Z L) :
        Set Z.regularAnalyticSpace) ⊆
        ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj (RegularCompactThomStage.Constructions.regularCompactImageComplement Z K) :
          Set Z.regularAnalyticSpace) from fun _ hx => hO hx)
      (Set.compl_subset_compl.mpr h) (RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage Z L)
      (RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage Z K) n)
    (GlobalSourceThomNaturality.Constructions.regularSourceThomSupportedGlobalIso_support_naturality Z a ha hO n)
    (relativeComplementChange_cast_naturality (TopCat.of Z.regularAmbientSpace)
      (show ((Z.regularThomComplementOpen ⊔ RegularCompactThomStage.Constructions.regularCompactImageComplement Z L : Opens Z.regularAmbientSpace) :
        Set Z.regularAmbientSpace) ⊆
        ((Z.regularThomComplementOpen ⊔ RegularCompactThomStage.Constructions.regularCompactImageComplement Z K : Opens Z.regularAmbientSpace) :
          Set Z.regularAmbientSpace) from sup_le_sup_left hO Z.regularThomComplementOpen)
      (Set.compl_subset_compl.mpr (OpenEmbeddingExtension.Constructions.embeddingCompactImage_mono (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) h))
      (RegularCompactThomStage.Constructions.regularCompactThom_unionComplement Z L) (RegularCompactThomStage.Constructions.regularCompactThom_unionComplement Z K) (2+n))

end

section

/-! The global normalized Thom pushforward on actual compactly supported source cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

def regularSourceCompactThomPushforward (n : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace) n ⟶
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) (2+n) :=
  AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomologyDesc (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace) n
    (fun K => (RegularCompactThomStage.Constructions.regularSourceCompactThomStageIso Z a ha K n).hom ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        (OpenEmbeddingExtension.Constructions.embeddingCompactImage (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) K) (2+n))
    (by
      intro K L h
      rw [← Category.assoc, regularSourceCompactThomStageIso_naturality,
        Category.assoc, AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap_ι])

theorem regularSourceCompactThomPushforward_stage (n : ℕ) (K : Compacts Z.regularAnalyticSpace) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace) K n ≫
        regularSourceCompactThomPushforward Z a ha n =
      (RegularCompactThomStage.Constructions.regularSourceCompactThomStageIso Z a ha K n).hom ≫
        AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
          (OpenEmbeddingExtension.Constructions.embeddingCompactImage (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) K) (2+n) :=
  AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyι_desc _ _ _ _ _ _

theorem regularSourceCompactThomPushforward_eq
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
    (hb : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 b = Z.regularThomClass) (n : ℕ) :
    regularSourceCompactThomPushforward Z a ha n = regularSourceCompactThomPushforward Z b hb n := by
  apply AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_hom_ext
  intro K
  rw [regularSourceCompactThomPushforward_stage, regularSourceCompactThomPushforward_stage,
    RegularCompactThomStage.Constructions.regularSourceCompactThomStageIso_eq Z a ha b hb]

end

/-! Actual zeroth singular homology is generated by classes from any open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false

def rationalZeroChainClass (X : TopCat.{0}) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X 0 →ₗ[ℚ] (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology 0 :=
  (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 0).comp
    ((LinearMap.id).codRestrict (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 0)
      (fun z => AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) z))

theorem rationalZeroChainClass_surjective (X : TopCat.{0}) : Function.Surjective (rationalZeroChainClass X) := by
  intro z
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 0 z
  exact ⟨c.val, rfl⟩

theorem rationalZeroChainClass_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X 0) :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 0 (rationalZeroChainClass X z) =
      rationalZeroChainClass Y ((AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) f).f 0 z) :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward_class f 0 ⟨z, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) z⟩

theorem rationalSingularChainMap_simplex {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) f).f n (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) (TopCat.toSSet.obj X) s) =
      AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) (TopCat.toSSet.obj Y) ((TopCat.toSSet.map f).app _ s) :=
  ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
      (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) s) 1

theorem singularZeroSimplex_open_lift (X : TopCat.{0}) (U : Opens X)
    (s : (TopCat.toSSet.obj X) _⦋0⦌) (hs : TopCat.toSSetObj₀Equiv s ∈ U) :
    ∃ t : (TopCat.toSSet.obj (TopCat.of U)) _⦋0⦌,
      (TopCat.toSSet.map U.inclusion').app _ t = s := by
  refine ⟨TopCat.toSSetObj₀Equiv.symm ⟨TopCat.toSSetObj₀Equiv s, hs⟩, ?_⟩
  change TopCat.toSSetObj₀Equiv.symm (TopCat.toSSetObj₀Equiv s) = s
  exact Equiv.symm_apply_apply _ s

theorem rationalHomologyZero_hom_ext_openCover (X : TopCat.{0}) {ι : Type*}
    (U : ι → Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i) {A : ModuleCat.{0} ℚ}
    {f g : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology 0 ⟶ A}
    (h : ∀ i, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (U i).inclusion' 0 ≫ f =
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (U i).inclusion' 0 ≫ g) : f = g := by
  have hz : f.hom.comp (rationalZeroChainClass X) = g.hom.comp (rationalZeroChainClass X) := by
    apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X) A
    intro s
    obtain ⟨i, hi⟩ := hcover (TopCat.toSSetObj₀Equiv s)
    obtain ⟨t, ht⟩ := singularZeroSimplex_open_lift X (U i) s hi
    have he := ConcreteCategory.congr_hom (h i)
      (rationalZeroChainClass (TopCat.of (U i)) (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) (TopCat.toSSet.obj (TopCat.of (U i))) t))
    simp only [ConcreteCategory.comp_apply] at he
    erw [rationalZeroChainClass_naturality, rationalSingularChainMap_simplex, ht] at he
    exact he
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := rationalZeroChainClass_surjective X z
  exact LinearMap.congr_fun hz z

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomZero.Constructions
