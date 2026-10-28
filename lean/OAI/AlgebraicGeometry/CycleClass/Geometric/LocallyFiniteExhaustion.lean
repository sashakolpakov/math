import OAI.AlgebraicGeometry.CycleClass.Geometric.SpatialExhaustion
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainCoefficients
import OAI.AlgebraicGeometry.CycleClass.Geometric.CoherentLifting
import OAI.Topology.Euclidean.Telescope

/-! # Locally Finite Exhaustion -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteExhaustion.Cycles

noncomputable section

/-!
# Locally finite chains and coherent relative chains along a compact exhaustion

The stages are the actual relative complexes C(X,X\K_i), and their transition
maps are induced by the identity maps of the complementary pairs. Compatible
sequences form an explicit chain complex with its coordinatewise differential.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Function
open scoped Simplicial Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (K : CompactExhaustion X)

/-- The actual ordinary relative-chain stage of a compact exhaustion. -/
abbrev exhaustionRelativeStage (i : ℕ) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  LocalHomology.Cycles.relativeSingularChains X (K i)ᶜ

/-- Transition maps are the genuine restrictions of the complementary pairs. -/
def exhaustionRelativeTransition (i : ℕ) :
    exhaustionRelativeStage X K (i + 1) ⟶ exhaustionRelativeStage X K i :=
  LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X (K.subset_succ i)

@[reassoc]
theorem exhaustionRelativeTransition_projection (i : ℕ) :
    LocalHomology.Cycles.relativeChainProjection X (K (i + 1))ᶜ ≫ exhaustionRelativeTransition X K i =
      LocalHomology.Cycles.relativeChainProjection X (K i)ᶜ :=
  LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction_projection X (K.subset_succ i)

/-- Every transition of actual relative chains is surjective in every degree. -/
theorem exhaustionRelativeTransition_surjective (i n : ℕ) :
    Function.Surjective ((exhaustionRelativeTransition X K i).f n) := by
  have hep : Epi ((LocalHomology.Cycles.relativeChainProjection X (K i)ᶜ).f n) :=
    (LocalHomology.Cycles.relativeChainSequence_degreewiseShortExact X (K i)ᶜ n).epi_g
  have hs := (ModuleCat.epi_iff_surjective ((LocalHomology.Cycles.relativeChainProjection X (K i)ᶜ).f n)).mp hep
  intro b
  obtain ⟨a, ha⟩ := hs b
  refine ⟨(LocalHomology.Cycles.relativeChainProjection X (K (i + 1))ᶜ).f n a, ?_⟩
  exact (ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (exhaustionRelativeTransition_projection X K i) n) a).trans ha

/-- The product uses the specified module structures of its actual relative-chain factors. -/
local instance exhaustionProductModule (n : ℕ) :
    Module ℤ (∀ i, (exhaustionRelativeStage X K i).X n) :=
  Pi.module ℕ (fun i => (exhaustionRelativeStage X K i).X n) ℤ

/-- Genuine compatible sequences of relative chains in one degree. -/
abbrev exhaustionCoherentChains (n : ℕ) : Submodule ℤ
    (∀ i, (exhaustionRelativeStage X K i).X n) :=
  Topology.Euclidean.Telescope.telescopeCompatible ℤ (fun i => (exhaustionRelativeStage X K i).X n)
    (fun i => ((exhaustionRelativeTransition X K i).f n).hom)

/-- Coherent sequences carry the inherited product-module structure. -/
local instance exhaustionCoherentModule (n : ℕ) :
    Module ℤ (exhaustionCoherentChains X K n) :=
  (exhaustionCoherentChains X K n).module

/-- The actual relative differentials preserve the compatibility equations. -/
def exhaustionCoherentDifferential (n m : ℕ) :
    exhaustionCoherentChains X K n →ₗ[ℤ] exhaustionCoherentChains X K m where
  toFun c := ⟨fun i => (exhaustionRelativeStage X K i).d n m (c.val i), by
    intro i
    change (exhaustionRelativeStage X K i).d n m (c.val i) =
      (exhaustionRelativeTransition X K i).f m
        ((exhaustionRelativeStage X K (i + 1)).d n m (c.val (i + 1)))
    rw [c.property i]
    exact ConcreteCategory.congr_hom ((exhaustionRelativeTransition X K i).comm n m)
      (c.val (i + 1))⟩
  map_add' c d := by
    apply Subtype.ext
    funext i
    exact ((exhaustionRelativeStage X K i).d n m).hom.map_add (c.val i) (d.val i)
  map_smul' r c := by
    apply Subtype.ext
    funext i
    exact ((exhaustionRelativeStage X K i).d n m).hom.map_smul r (c.val i)

@[simp]
theorem exhaustionCoherentDifferential_apply (n m : ℕ)
    (c : exhaustionCoherentChains X K n) (i : ℕ) :
    (exhaustionCoherentDifferential X K n m c).val i =
      (exhaustionRelativeStage X K i).d n m (c.val i) := rfl

/-- The explicit chain complex of coherent actual relative chains. -/
def exhaustionCoherentComplex : ChainComplex (ModuleCat.{0} ℤ) ℕ where
  X n := ModuleCat.of ℤ (exhaustionCoherentChains X K n)
  d n m := ModuleCat.ofHom (exhaustionCoherentDifferential X K n m)
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    funext i
    change (exhaustionRelativeStage X K i).d n m (c.val i) = 0
    rw [(exhaustionRelativeStage X K i).shape n m h]
    rfl
  d_comp_d' n m k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    funext i
    exact ConcreteCategory.congr_hom ((exhaustionRelativeStage X K i).d_comp_d n m k)
      (c.val i)

/-- Projection of a coherent chain to one actual relative-chain stage. -/
def exhaustionCoherentProjection (i : ℕ) :
    exhaustionCoherentComplex X K ⟶ exhaustionRelativeStage X K i where
  f n := ModuleCat.ofHom ((LinearMap.proj i).comp (exhaustionCoherentChains X K n).subtype)
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    rfl

@[simp]
theorem exhaustionCoherentProjection_apply (i n : ℕ)
    (c : exhaustionCoherentChains X K n) :
    (exhaustionCoherentProjection X K i).f n c = c.val i := rfl

@[reassoc]
theorem exhaustionCoherentProjection_compatibility (i : ℕ) :
    exhaustionCoherentProjection X K (i + 1) ≫ exhaustionRelativeTransition X K i =
      exhaustionCoherentProjection X K i := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact (c.property i).symm

/-- Compatible maps into the relative stages lift to the coherent complex. -/
def exhaustionCoherentLift {C : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : ∀ i, C ⟶ exhaustionRelativeStage X K i)
    (hf : ∀ i, f (i + 1) ≫ exhaustionRelativeTransition X K i = f i) :
    C ⟶ exhaustionCoherentComplex X K where
  f n := ModuleCat.ofHom
    { toFun := fun c => ⟨fun i => (f i).f n c, by
        intro i
        exact (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom (hf i) n) c).symm⟩
      map_add' := by
        intro c d
        apply Subtype.ext
        funext i
        exact ((f i).f n).hom.map_add c d
      map_smul' := by
        intro r c
        apply Subtype.ext
        funext i
        exact ((f i).f n).hom.map_smul r c }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    funext i
    exact ConcreteCategory.congr_hom ((f i).comm n m) c

@[reassoc]
theorem exhaustionCoherentLift_projection {C : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : ∀ i, C ⟶ exhaustionRelativeStage X K i)
    (hf : ∀ i, f (i + 1) ≫ exhaustionRelativeTransition X K i = f i) (i : ℕ) :
    exhaustionCoherentLift X K f hf ≫ exhaustionCoherentProjection X K i = f i := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

/-- The compatible lift is unique, giving the explicit inverse-limit universal property. -/
theorem exhaustionCoherentLift_unique {C : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : ∀ i, C ⟶ exhaustionRelativeStage X K i)
    (hf : ∀ i, f (i + 1) ≫ exhaustionRelativeTransition X K i = f i)
    (g : C ⟶ exhaustionCoherentComplex X K)
    (hg : ∀ i, g ≫ exhaustionCoherentProjection X K i = f i) :
    g = exhaustionCoherentLift X K f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  funext i
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom (hg i) n) c

/-- Actual compact restrictions form a compatible map into the exhaustion tower. -/
def locallyFiniteToExhaustion :
    LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X ⟶ exhaustionCoherentComplex X K :=
  exhaustionCoherentLift X K
    (fun i => LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction X (K i) (K.isCompact i))
    (fun i => LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction_subset X
      (K.isCompact i) (K.isCompact (i + 1)) (K.subset_succ i))

/-- The degree map of the canonical compact-restriction comparison. -/
abbrev locallyFiniteToExhaustionDegree (n : ℕ) :
    LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n →ₗ[ℤ] exhaustionCoherentChains X K n :=
  ((locallyFiniteToExhaustion X K).f n).hom

@[simp]
theorem locallyFiniteToExhaustionDegree_apply (n : ℕ)
    (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n) (i : ℕ) :
    (locallyFiniteToExhaustionDegree X K n c).val i =
      LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestrictionDegree X (K i) (K.isCompact i) n c := rfl

@[reassoc]
theorem locallyFiniteToExhaustion_projection (i : ℕ) :
    locallyFiniteToExhaustion X K ≫ exhaustionCoherentProjection X K i =
      LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction X (K i) (K.isCompact i) :=
  exhaustionCoherentLift_projection X K _ _ i

/-- Finite coefficient systems use their inherited function-module structure. -/
local instance exhaustionCoefficientModule (n : ℕ) :
    Module ℤ (SpatialExhaustion.Cycles.SpatialSupport.coherentExhaustionCoefficients ℤ (LocallyFiniteChains.Cycles.singularSimplexImage X n) K) :=
  (SpatialExhaustion.Cycles.SpatialSupport.coherentExhaustionCoefficients ℤ (LocallyFiniteChains.Cycles.singularSimplexImage X n) K).module

/-- The genuine relative quotient coefficients of a coherent relative-chain family. -/
def exhaustionRelativeToCoefficients (n : ℕ) :
    exhaustionCoherentChains X K n →ₗ[ℤ]
      SpatialExhaustion.Cycles.SpatialSupport.coherentExhaustionCoefficients ℤ (LocallyFiniteChains.Cycles.singularSimplexImage X n) K where
  toFun c := ⟨fun i => (RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K i) n (c.val i)).val, by
    constructor
    · intro i σ hσ
      exact (Finsupp.mem_supported' ℤ _).1
        (RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K i) n (c.val i)).property σ hσ
    · intro i σ hσ
      change (RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K (i + 1)) n (c.val (i + 1))).val σ =
        (RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K i) n (c.val i)).val σ
      rw [c.property i]
      exact (RelativeChainCoefficients.Cycles.relativeChainCoefficients_restriction_of_meets X n (K.subset_succ i)
        (c.val (i + 1)) σ hσ).symm⟩
  map_add' c d := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val ((RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K i) n).map_add (c.val i) (d.val i))
  map_smul' r c := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val ((RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K i) n).map_smul r (c.val i))

/-- Each coherent finite family has the proved support required by the genuine
relative-chain coefficient equivalence. -/
def exhaustionSupportedCoefficients (n : ℕ)
    (c : SpatialExhaustion.Cycles.SpatialSupport.coherentExhaustionCoefficients ℤ (LocallyFiniteChains.Cycles.singularSimplexImage X n) K)
    (i : ℕ) : Finsupp.supported ℤ ℤ
      {σ | (LocallyFiniteChains.Cycles.singularSimplexImage X n σ ∩ K i).Nonempty} :=
  ⟨c.val i, (Finsupp.mem_supported' ℤ _).2 (c.property.1 i)⟩

/-- Reinterpret coherent finite stage coefficients as actual relative chains. -/
def exhaustionRelativeFromCoefficients (n : ℕ)
    (c : SpatialExhaustion.Cycles.SpatialSupport.coherentExhaustionCoefficients ℤ (LocallyFiniteChains.Cycles.singularSimplexImage X n) K) :
    exhaustionCoherentChains X K n :=
  ⟨fun i => (RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K i) n).symm
    (exhaustionSupportedCoefficients X K n c i), by
    intro i
    apply (RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K i) n).injective
    apply Subtype.ext
    apply Finsupp.ext
    intro σ
    change _ = (RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K i) n
      ((LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X (K.subset_succ i)).f n _)).val σ
    rw [RelativeChainCoefficients.Cycles.relativeChainCoefficients_restriction_apply]
    simp only [LinearEquiv.apply_symm_apply]
    split_ifs with hσ
    · exact (c.property.2 i σ hσ).symm
    · exact c.property.1 i σ hσ⟩

theorem exhaustionRelativeFromTo (n : ℕ) (c : exhaustionCoherentChains X K n) :
    exhaustionRelativeFromCoefficients X K n (exhaustionRelativeToCoefficients X K n c) = c := by
  apply Subtype.ext
  funext i
  change (RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K i) n).symm
    (RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K i) n (c.val i)) = c.val i
  exact (RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K i) n).symm_apply_apply (c.val i)

theorem exhaustionRelativeToFrom (n : ℕ)
    (c : SpatialExhaustion.Cycles.SpatialSupport.coherentExhaustionCoefficients ℤ (LocallyFiniteChains.Cycles.singularSimplexImage X n) K) :
    exhaustionRelativeToCoefficients X K n (exhaustionRelativeFromCoefficients X K n c) = c := by
  apply Subtype.ext
  funext i
  apply Finsupp.ext
  intro σ
  change (RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K i) n
    ((RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K i) n).symm
      (exhaustionSupportedCoefficients X K n c i))).val σ = c.val i σ
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Actual coherent relative chains have exactly the coherent finite coefficients
used in the explicit locally finite reconstruction. -/
def exhaustionRelativeCoefficientsEquiv (n : ℕ) :
    exhaustionCoherentChains X K n ≃ₗ[ℤ]
      SpatialExhaustion.Cycles.SpatialSupport.coherentExhaustionCoefficients ℤ (LocallyFiniteChains.Cycles.singularSimplexImage X n) K where
  toFun := exhaustionRelativeToCoefficients X K n
  invFun := exhaustionRelativeFromCoefficients X K n
  left_inv := exhaustionRelativeFromTo X K n
  right_inv := exhaustionRelativeToFrom X K n
  map_add' := (exhaustionRelativeToCoefficients X K n).map_add
  map_smul' := (exhaustionRelativeToCoefficients X K n).map_smul

/-- The relative stages of the canonical chain map have precisely the finite
compact truncations of the original locally finite coefficients. -/
theorem locallyFiniteToExhaustion_coefficients (n : ℕ)
    (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n) :
    exhaustionRelativeCoefficientsEquiv X K n (locallyFiniteToExhaustionDegree X K n c) =
      SpatialExhaustion.Cycles.SpatialSupport.toExhaustionCoefficients (LocallyFiniteChains.Cycles.singularSimplexImage X n) K c := by
  apply Subtype.ext
  funext i
  apply Finsupp.ext
  intro σ
  change (RelativeChainCoefficients.Cycles.relativeChainCoefficients X (K i) n
    ((LocalHomology.Cycles.relativeChainProjection X (K i)ᶜ).f n
      (LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactTruncation X (K i) (K.isCompact i) n c))).val σ =
        if (LocallyFiniteChains.Cycles.singularSimplexImage X n σ ∩ K i).Nonempty then c σ else 0
  rw [RelativeChainCoefficients.Cycles.relativeChainCoefficients_projection_apply, LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactTruncation_coefficients]
  split_ifs <;> rfl

/-- Degreewise reconstruction identifies actual locally finite singular chains
with compatible actual relative chains along the compact exhaustion. -/
def locallyFiniteExhaustionDegreeEquiv (n : ℕ) :
    LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n ≃ₗ[ℤ] exhaustionCoherentChains X K n :=
  (SpatialExhaustion.Cycles.SpatialSupport.exhaustionCoefficientsEquiv (LocallyFiniteChains.Cycles.singularSimplexImage X n) K
    (LocallyFiniteChains.Cycles.singularSimplexImage_nonempty X n)).trans (exhaustionRelativeCoefficientsEquiv X K n).symm

/-- The explicit equivalence is the previously constructed compact-restriction map. -/
theorem locallyFiniteExhaustionDegreeEquiv_eq (n : ℕ) :
    (locallyFiniteExhaustionDegreeEquiv X K n).toLinearMap =
      locallyFiniteToExhaustionDegree X K n := by
  apply LinearMap.ext
  intro c
  apply (exhaustionRelativeCoefficientsEquiv X K n).injective
  change (exhaustionRelativeCoefficientsEquiv X K n)
      ((exhaustionRelativeCoefficientsEquiv X K n).symm
        (SpatialExhaustion.Cycles.SpatialSupport.toExhaustionCoefficients (LocallyFiniteChains.Cycles.singularSimplexImage X n) K c)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (locallyFiniteToExhaustion_coefficients X K n c).symm

/-- The actual locally finite singular complex is the coherent relative-chain
complex of any genuine compact exhaustion. -/
def locallyFiniteExhaustionIso :
    LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X ≅ exhaustionCoherentComplex X K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (locallyFiniteExhaustionDegreeEquiv X K n).toModuleIso)
    (by
      intro n m _
      change ModuleCat.ofHom (locallyFiniteExhaustionDegreeEquiv X K n).toLinearMap ≫
          (exhaustionCoherentComplex X K).d n m =
        (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).d n m ≫
          ModuleCat.ofHom (locallyFiniteExhaustionDegreeEquiv X K m).toLinearMap
      rw [locallyFiniteExhaustionDegreeEquiv_eq, locallyFiniteExhaustionDegreeEquiv_eq]
      exact (locallyFiniteToExhaustion X K).comm n m)

@[simp]
theorem locallyFiniteExhaustionIso_hom :
    (locallyFiniteExhaustionIso X K).hom = locallyFiniteToExhaustion X K := by
  apply HomologicalComplex.hom_ext
  intro n
  change ModuleCat.ofHom (locallyFiniteExhaustionDegreeEquiv X K n).toLinearMap = _
  rw [locallyFiniteExhaustionDegreeEquiv_eq]
  rfl

@[reassoc]
theorem locallyFiniteExhaustionIso_projection (i : ℕ) :
    (locallyFiniteExhaustionIso X K).hom ≫ exhaustionCoherentProjection X K i =
      LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction X (K i) (K.isCompact i) := by
  rw [locallyFiniteExhaustionIso_hom, locallyFiniteToExhaustion_projection]

/-- Compact restrictions are jointly injective on the actual locally finite chains. -/
theorem locallyFiniteExhaustion_jointly_injective (n : ℕ) :
    Function.Injective (fun c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n =>
      fun i => (LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction X (K i) (K.isCompact i)).f n c) := by
  intro a b h
  apply (locallyFiniteExhaustionDegreeEquiv X K n).injective
  change (locallyFiniteExhaustionDegreeEquiv X K n).toLinearMap a =
    (locallyFiniteExhaustionDegreeEquiv X K n).toLinearMap b
  rw [locallyFiniteExhaustionDegreeEquiv_eq]
  apply Subtype.ext
  exact h

/-- Every compatible family of actual relative chains lifts to a locally finite
chain with exactly those compact restrictions. -/
theorem locallyFiniteExhaustion_lift (n : ℕ)
    (a : ∀ i, (exhaustionRelativeStage X K i).X n)
    (ha : ∀ i, (exhaustionRelativeTransition X K i).f n (a (i + 1)) = a i) :
    ∃ b : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n,
      ∀ i, (LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction X (K i) (K.isCompact i)).f n b = a i := by
  let c : exhaustionCoherentChains X K n := ⟨a, fun i => (ha i).symm⟩
  refine ⟨(locallyFiniteExhaustionDegreeEquiv X K n).symm c, ?_⟩
  have h := (locallyFiniteExhaustionDegreeEquiv X K n).apply_symm_apply c
  change (locallyFiniteExhaustionDegreeEquiv X K n).toLinearMap
    ((locallyFiniteExhaustionDegreeEquiv X K n).symm c) = c at h
  rw [locallyFiniteExhaustionDegreeEquiv_eq] at h
  intro i
  exact congrArg (fun z : exhaustionCoherentChains X K n => z.val i) h

/-- The corresponding isomorphism concerns the homology of the actual coherent
chain complex; no commutation of homology with inverse limits is assumed. -/
def locallyFiniteExhaustionHomologyIso (n : ℕ) :
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology n ≅
      (exhaustionCoherentComplex X K).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
    (locallyFiniteExhaustionIso X K)

/-- Coherent actual relative-homology classes along a compact exhaustion lift
to an actual locally finite homology class. No levelwise vanishing is needed
for existence. -/
theorem exists_locallyFinite_homology_class_of_coherent_exhaustion (n : ℕ)
    (c : ∀ i, (exhaustionRelativeStage X K i).homology n)
    (hc : ∀ i, HomologicalComplex.homologyMap (exhaustionRelativeTransition X K i) n
      (c (i + 1)) = c i) :
    ∃ a : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology n,
      ∀ i, LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction X (K i) (K.isCompact i) n a = c i :=
  CoherentLifting.Cycles.exists_homology_class_of_coherent_classes
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X) (exhaustionRelativeStage X K)
    (exhaustionRelativeTransition X K)
    (fun i => LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction X (K i) (K.isCompact i)) n
    (fun i => exhaustionRelativeTransition_surjective X K i (n + 1))
    (locallyFiniteExhaustion_jointly_injective X K) (locallyFiniteExhaustion_lift X K) c hc

/-- When the next relative-homology degree vanishes at every stage, compact
restrictions determine a locally finite homology class uniquely. -/
theorem locallyFinite_homology_class_eq_of_exhaustion_restrictions (n : ℕ)
    (hvanish : ∀ i, IsZero ((exhaustionRelativeStage X K i).homology (n + 1)))
    (a b : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology n)
    (hab : ∀ i, LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction X (K i) (K.isCompact i) n a =
      LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction X (K i) (K.isCompact i) n b) : a = b :=
  CoherentLifting.Cycles.homology_class_eq_of_coherent_projections
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X) (exhaustionRelativeStage X K)
    (exhaustionRelativeTransition X K)
    (fun i => LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction X (K i) (K.isCompact i)) n
    (fun i => exhaustionRelativeTransition_surjective X K i (n + 2)) hvanish
    (fun i => LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction_subset X
      (K.isCompact i) (K.isCompact (i + 1)) (K.subset_succ i))
    (locallyFiniteExhaustion_jointly_injective X K) (locallyFiniteExhaustion_lift X K) a b hab

/-- The existence and uniqueness theorem for an actual coherent family of
relative classes, with the next-degree vanishing stated explicitly. It does
not assert the existence of geometric fundamental classes at the stages. -/
theorem existsUnique_locallyFinite_homology_class_of_coherent_exhaustion (n : ℕ)
    (hvanish : ∀ i, IsZero ((exhaustionRelativeStage X K i).homology (n + 1)))
    (c : ∀ i, (exhaustionRelativeStage X K i).homology n)
    (hc : ∀ i, HomologicalComplex.homologyMap (exhaustionRelativeTransition X K i) n
      (c (i + 1)) = c i) :
    ∃! a : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology n,
      ∀ i, LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction X (K i) (K.isCompact i) n a = c i :=
  CoherentLifting.Cycles.existsUnique_homology_class_of_coherent_classes
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X) (exhaustionRelativeStage X K)
    (exhaustionRelativeTransition X K)
    (fun i => LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction X (K i) (K.isCompact i)) n
    (exhaustionRelativeTransition_surjective X K) hvanish
    (fun i => LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction_subset X
      (K.isCompact i) (K.isCompact (i + 1)) (K.subset_succ i))
    (locallyFiniteExhaustion_jointly_injective X K) (locallyFiniteExhaustion_lift X K) c hc

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteExhaustion.Cycles
