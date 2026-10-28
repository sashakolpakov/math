import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact
import OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Small Mayer Vietoris -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles

noncomputable section

/-!
# Mayer–Vietoris for the actual binary-cover small singular chains

The union here consists of simplices whose entire image is in one of the two
subsets. It is not the full singular set of the union. The short exact sequence
and its homology sequence do not assume the small-to-all quasi-isomorphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

/-- The ordinary integral chain functor on simplicial sets. -/
abbrev integralSimplicialChainFunctor : SSet.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- The ordinary simplicial chain functor preserves colimits degree by degree. -/
instance integralSimplicialChainFunctor_preservesColimits :
    PreservesColimits integralSimplicialChainFunctor where
  preservesColimitsOfShape {J _} := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    change PreservesColimitsOfShape J
      ((evaluation SimplexCategoryᵒᵖ (Type)).obj (.op ⦋n⦌) ⋙
        sigmaConst.obj (ModuleCat.of ℤ ℤ))
    infer_instance

instance integralSimplicialChainFunctor_preservesMonomorphisms :
    integralSimplicialChainFunctor.PreservesMonomorphisms where
  preserves f _ := by
    dsimp [integralSimplicialChainFunctor, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono

/-- Inclusion of one actual subspace in another. -/
def subsetInclusion (X : TopCat.{0}) {U V : Set X} (h : U ⊆ V) :
    TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩

instance subsetInclusion_mono (X : TopCat.{0}) {U V : Set X} (h : U ⊆ V) :
    Mono (subsetInclusion X h) :=
  (TopCat.mono_iff_injective _).mpr (Set.inclusion_injective h)

/-- The image of the singular set of a genuine subspace in the ambient singular set. -/
abbrev subspaceSingularSubcomplex (X : TopCat.{0}) (U : Set X) :
    (TopCat.toSSet.obj X).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X U))

/-- Image membership is exactly containment of the whole singular simplex in the subspace. -/
theorem mem_subspaceSingularSubcomplex (X : TopCat.{0}) (U : Set X)
    (n : SimplexCategoryᵒᵖ) (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (subspaceSingularSubcomplex X U).obj n ↔
      Set.range (X.toSSetObjEquiv n σ) ⊆ U := by
  constructor
  · rintro ⟨τ, rfl⟩ y ⟨z, rfl⟩
    exact (((TopCat.of U).toSSetObjEquiv n τ) z).property
  · intro hσ
    let τ : C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), U) :=
      ⟨fun z => ⟨X.toSSetObjEquiv n σ z, hσ ⟨z, rfl⟩⟩,
        (X.toSSetObjEquiv n σ).continuous.subtype_mk _⟩
    refine ⟨((TopCat.of U).toSSetObjEquiv n).symm τ, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    ext z
    rfl

/-- The contained-simplex subcomplex is the actual singular set of the subspace. -/
def subspaceSingularSetIso (X : TopCat.{0}) (U : Set X) :
    TopCat.toSSet.obj (TopCat.of U) ≅ (subspaceSingularSubcomplex X U : SSet) :=
  asIso (SSet.Subcomplex.toRange (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X U)))

/-- Containment in an intersection is the intersection of the two simplex conditions. -/
theorem subspaceSingularSubcomplex_inter (X : TopCat.{0}) (U V : Set X) :
    subspaceSingularSubcomplex X (U ∩ V) =
      subspaceSingularSubcomplex X U ⊓ subspaceSingularSubcomplex X V := by
  ext n σ
  change σ ∈ (subspaceSingularSubcomplex X (U ∩ V)).obj n ↔
    σ ∈ (subspaceSingularSubcomplex X U).obj n ∧
      σ ∈ (subspaceSingularSubcomplex X V).obj n
  rw [mem_subspaceSingularSubcomplex, mem_subspaceSingularSubcomplex,
    mem_subspaceSingularSubcomplex]
  exact Set.subset_inter_iff

/-- Simplices subordinate to the binary family, requiring one whole-image containment. -/
abbrev binarySmallSingularSubcomplex (X : TopCat.{0}) (U V : Set X) :
    (TopCat.toSSet.obj X).Subcomplex :=
  subspaceSingularSubcomplex X U ⊔ subspaceSingularSubcomplex X V

/-- This is the same small-simplex construction used by the comparison infrastructure. -/
theorem binarySmallSingularSubcomplex_eq (X : TopCat.{0}) (U V : Set X) :
    binarySmallSingularSubcomplex X U V =
      OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X (fun b : Bool => if b then V else U) := by
  ext n σ
  change (σ ∈ (subspaceSingularSubcomplex X U).obj n ∨
      σ ∈ (subspaceSingularSubcomplex X V).obj n) ↔
    ∃ b : Bool, Set.range (X.toSSetObjEquiv n σ) ⊆ if b then V else U
  rw [mem_subspaceSingularSubcomplex, mem_subspaceSingularSubcomplex]
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨b, h⟩
    cases b
    · exact Or.inl h
    · exact Or.inr h

/-- Singular simplices of the first subspace, viewed as small ambient simplices. -/
def binarySmallSingularLeft (X : TopCat.{0}) (U V : Set X) :
    TopCat.toSSet.obj (TopCat.of U) ⟶ (binarySmallSingularSubcomplex X U V : SSet) :=
  (subspaceSingularSetIso X U).hom ≫ SSet.Subcomplex.homOfLE le_sup_left

/-- Singular simplices of the second subspace, viewed as small ambient simplices. -/
def binarySmallSingularRight (X : TopCat.{0}) (U V : Set X) :
    TopCat.toSSet.obj (TopCat.of V) ⟶ (binarySmallSingularSubcomplex X U V : SSet) :=
  (subspaceSingularSetIso X V).hom ≫ SSet.Subcomplex.homOfLE le_sup_right

/-- The binary small singular set is the pushout of the two genuine subspace
singular sets over the genuine singular set of their intersection. -/
theorem binarySmallSingular_isPushout (X : TopCat.{0}) (U V : Set X) :
    IsPushout (TopCat.toSSet.map (subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U)))
      (TopCat.toSSet.map (subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V)))
      (binarySmallSingularLeft X U V) (binarySmallSingularRight X U V) := by
  let sq : SSet.Subcomplex.BicartSq (subspaceSingularSubcomplex X (U ∩ V))
      (subspaceSingularSubcomplex X U) (subspaceSingularSubcomplex X V)
      (binarySmallSingularSubcomplex X U V) :=
    ⟨rfl, (subspaceSingularSubcomplex_inter X U V).symm⟩
  exact sq.isPushout.of_iso'
    (subspaceSingularSetIso X (U ∩ V)) (subspaceSingularSetIso X U)
    (subspaceSingularSetIso X V) (Iso.refl _)
    (by ext n σ; rfl) (by ext n σ; rfl) (by simp [binarySmallSingularLeft])
    (by simp [binarySmallSingularRight])

/-- Actual integral chains generated by simplices lying wholly in one of the two subsets. -/
abbrev binarySmallSingularChains (X : TopCat.{0}) (U V : Set X) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  integralSimplicialChainFunctor.obj (binarySmallSingularSubcomplex X U V : SSet)

/-- The homology of the actual binary-cover small chain complex. -/
abbrev binarySmallSingularHomology (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    ModuleCat.{0} ℤ := (binarySmallSingularChains X U V).homology n

/-- The singular-set pushout remains a pushout after forming integral chains. -/
theorem binarySmallChain_isPushout (X : TopCat.{0}) (U V : Set X) :
    IsPushout
      (LocalHomology.Cycles.integralSingularChainFunctor.map
        (subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U)))
      (LocalHomology.Cycles.integralSingularChainFunctor.map
        (subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V)))
      (integralSimplicialChainFunctor.map (binarySmallSingularLeft X U V))
      (integralSimplicialChainFunctor.map (binarySmallSingularRight X U V)) :=
  integralSimplicialChainFunctor.map_isPushout (binarySmallSingular_isPushout X U V)

/-- The genuine small-chain sequence `C(U∩V) → C(U)⊕C(V) → C_small(U,V)`.
The first arrow uses the two inclusions with signs `(+,-)`; the second adds them. -/
def smallMayerVietorisSequence (X : TopCat.{0}) (U V : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  (binarySmallChain_isPushout X U V).shortComplex

@[simp]
theorem smallMayerVietorisSequence_f (X : TopCat.{0}) (U V : Set X) :
    (smallMayerVietorisSequence X U V).f =
      biprod.lift
        (LocalHomology.Cycles.integralSingularChainFunctor.map
          (subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U)))
        (-LocalHomology.Cycles.integralSingularChainFunctor.map
          (subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V))) := rfl

@[simp]
theorem smallMayerVietorisSequence_g (X : TopCat.{0}) (U V : Set X) :
    (smallMayerVietorisSequence X U V).g =
      biprod.desc
        (integralSimplicialChainFunctor.map (binarySmallSingularLeft X U V))
        (integralSimplicialChainFunctor.map (binarySmallSingularRight X U V)) := rfl

/-- The small-chain sequence is short exact, with no excision or subdivision hypothesis. -/
theorem smallMayerVietorisSequence_shortExact (X : TopCat.{0}) (U V : Set X) :
    (smallMayerVietorisSequence X U V).ShortExact := by
  have hm : Mono (LocalHomology.Cycles.integralSingularChainFunctor.map
      (subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U))) := by
    change Mono (integralSimplicialChainFunctor.map
      (TopCat.toSSet.map (subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U))))
    infer_instance
  have : Mono (smallMayerVietorisSequence X U V).f := by
    rw [smallMayerVietorisSequence_f]
    exact @mono_of_mono_fac _ _ _ _ _ _ _ _ hm (biprod.lift_fst _ _)
  have : Epi (smallMayerVietorisSequence X U V).g :=
    (binarySmallChain_isPushout X U V).epi_shortComplex_g
  exact { exact := (binarySmallChain_isPushout X U V).exact_shortComplex }

/-- The short exact sequence is exact in every actual chain degree. -/
theorem smallMayerVietorisSequence_degreewiseShortExact
    (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    ((smallMayerVietorisSequence X U V).map
      (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (smallMayerVietorisSequence_shortExact X U V) n

/-- The middle homology object has its canonical direct-sum interpretation. -/
def smallMayerVietorisMiddleHomologyIso (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    (smallMayerVietorisSequence X U V).X₂.homology n ≅
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of U) n ⊞
        RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of V) n := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n
  letI : PreservesBinaryBiproduct
      (LocalHomology.Cycles.integralSingularChains (TopCat.of U)) (LocalHomology.Cycles.integralSingularChains (TopCat.of V)) F :=
    preservesBinaryBiproduct_of_preservesBiproduct F _ _
  exact F.mapBiprod _ _

set_option backward.isDefEq.respectTransparency false in
/-- In the direct-sum description, the first component is the usual inclusion map. -/
@[reassoc]
theorem smallMayerVietoris_homology_f_fst (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (smallMayerVietorisSequence X U V).f n ≫
      (smallMayerVietorisMiddleHomologyIso X U V n).hom ≫ biprod.fst =
        RelativeHomologyExact.Cycles.integralSingularHomologyMap
          (subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U)) n := by
  have h : (smallMayerVietorisMiddleHomologyIso X U V n).hom ≫ biprod.fst =
      HomologicalComplex.homologyMap biprod.fst n := by
    exact biprod.lift_fst _ _
  rw [h, ← HomologicalComplex.homologyMap_comp, smallMayerVietorisSequence_f,
    biprod.lift_fst]

set_option backward.isDefEq.respectTransparency false in
/-- In the direct-sum description, the second inclusion carries the opposite sign. -/
@[reassoc]
theorem smallMayerVietoris_homology_f_snd (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (smallMayerVietorisSequence X U V).f n ≫
      (smallMayerVietorisMiddleHomologyIso X U V n).hom ≫ biprod.snd =
        -RelativeHomologyExact.Cycles.integralSingularHomologyMap
          (subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V)) n := by
  have h : (smallMayerVietorisMiddleHomologyIso X U V n).hom ≫ biprod.snd =
      HomologicalComplex.homologyMap biprod.snd n := by
    exact biprod.lift_snd _ _
  rw [h, ← HomologicalComplex.homologyMap_comp, smallMayerVietorisSequence_f,
    biprod.lift_snd, HomologicalComplex.homologyMap_neg]

/-- The genuine connecting map from small homology to intersection homology. -/
def smallMayerVietorisBoundary (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    binarySmallSingularHomology X U V (n + 1) ⟶
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (U ∩ V : Set X)) n :=
  (smallMayerVietorisSequence_shortExact X U V).δ (n + 1) n rfl

/-- Six consecutive terms of the small-chain Mayer–Vietoris homology sequence. -/
def smallMayerVietorisHomologySequence (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    ComposableArrows (ModuleCat.{0} ℤ) 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    (smallMayerVietorisSequence_shortExact X U V) (n + 1) n rfl

/-- Exactness of the six-term sequence; the middle objects are canonically the
sums of the two subspace homologies via `smallMayerVietorisMiddleHomologyIso`. -/
theorem smallMayerVietorisHomologySequence_exact
    (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    (smallMayerVietorisHomologySequence X U V n).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact
    (smallMayerVietorisSequence_shortExact X U V) (n + 1) n rfl

/-- Exactness at the homology of the two subspaces. -/
theorem smallMayerVietoris_range_left (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    LinearMap.range (HomologicalComplex.homologyMap (smallMayerVietorisSequence X U V).f n).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (smallMayerVietorisSequence X U V).g n).hom :=
  ((smallMayerVietorisSequence_shortExact X U V).homology_exact₂ n).moduleCat_range_eq_ker

/-- A small homology class comes from the subspace sum exactly when its boundary vanishes. -/
theorem smallMayerVietoris_range_middle (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    LinearMap.range
      (HomologicalComplex.homologyMap (smallMayerVietorisSequence X U V).g (n + 1)).hom =
        LinearMap.ker (smallMayerVietorisBoundary X U V n).hom :=
  ((smallMayerVietorisSequence_shortExact X U V).homology_exact₃
    (n + 1) n rfl).moduleCat_range_eq_ker

/-- An intersection class is a small-homology boundary exactly when it dies in both subspaces. -/
theorem smallMayerVietoris_range_boundary (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    LinearMap.range (smallMayerVietorisBoundary X U V n).hom =
      LinearMap.ker
        (HomologicalComplex.homologyMap (smallMayerVietorisSequence X U V).f n).hom :=
  ((smallMayerVietorisSequence_shortExact X U V).homology_exact₁
    (n + 1) n rfl).moduleCat_range_eq_ker

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles
