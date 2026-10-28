import OAI.AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Category.TopCat.Opens

/-! # Open Rational -/

namespace OAI.AlgebraicTopology.Duality.Poincare.OpenRational

noncomputable section

/-!
# Ordinary rational Mayer--Vietoris on native open subspaces

The pullback opens in the union form an actual cover. Their subspaces are
canonically homeomorphic to the original opens and their intersection.
Transport of the proved ordinary rational sequence gives the native sequence,
with the actual inclusion signs (+,-) and the sum of the inclusion images.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : TopCat.{0}}

/-- Ordinary rational homology of the actual open subspace. -/
abbrev openRationalHomology (U : Opens X) (n : ℕ) : ModuleCat.{0} ℚ :=
  (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).homology n

/-- Pushforward by the literal inclusion of two native open subspaces. -/
abbrev openRationalHomologyMap {U V : Opens X} (h : U ≤ V) (n : ℕ) :
    openRationalHomology U n ⟶ openRationalHomology V n :=
  Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (TopCat.ofHom (ContinuousMap.inclusion h)) n

namespace OpenRationalMayerVietoris

/-- Rational singular homology as its actual covariant functor. -/
abbrev homologyFunctor (n : ℕ) : TopCat.{0} ⥤ ModuleCat.{0} ℚ :=
  AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n

/-- Flatten the actual pullback of an open subspace inside a larger open. -/
def preimageHomeomorph {U W : Opens X} (h : U ≤ W) :
    ((Subtype.val : W → X) ⁻¹' (U : Set X)) ≃ₜ U :=
  Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange (by
    rw [Subtype.range_val]
    exact h)

/-- The flattening homeomorphism induces an actual ordinary homology isomorphism. -/
def preimageHomologyIso {U W : Opens X} (h : U ≤ W) (n : ℕ) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (TopCat.of ((Subtype.val : W → X) ⁻¹' (U : Set X)))).homology n ≅
      openRationalHomology U n :=
  (OpenRationalMayerVietoris.homologyFunctor n).mapIso (TopCat.isoOfHomeo (preimageHomeomorph h))

/-- Flattening pullback subspaces respects every actual nested inclusion. -/
@[reassoc]
theorem preimageHomologyIso_naturality {U V W : Opens X}
    (hUV : U ≤ V) (hVW : V ≤ W) (n : ℕ) :
    Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion (TopCat.of W)
          (show (Subtype.val : W → X) ⁻¹' (U : Set X) ⊆
            (Subtype.val : W → X) ⁻¹' (V : Set X) from fun _ hx => hUV hx)) n ≫
        (preimageHomologyIso hVW n).hom =
      (preimageHomologyIso (hUV.trans hVW) n).hom ≫ openRationalHomologyMap hUV n := by
  change (OpenRationalMayerVietoris.homologyFunctor n).map _ ≫ (OpenRationalMayerVietoris.homologyFunctor n).map _ =
    (OpenRationalMayerVietoris.homologyFunctor n).map _ ≫ (OpenRationalMayerVietoris.homologyFunctor n).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (OpenRationalMayerVietoris.homologyFunctor n).map
  ext x
  rfl

/-- Flattening respects inclusion in the surrounding open subspace. -/
@[reassoc]
theorem preimageHomologyIso_ambient {U W : Opens X} (h : U ≤ W) (n : ℕ) :
    (preimageHomologyIso h n).hom ≫ openRationalHomologyMap h n =
      Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of W) ((Subtype.val : W → X) ⁻¹' (U : Set X))) n := by
  change (OpenRationalMayerVietoris.homologyFunctor n).map _ ≫ (OpenRationalMayerVietoris.homologyFunctor n).map _ = (OpenRationalMayerVietoris.homologyFunctor n).map _
  rw [← Functor.map_comp]
  apply congrArg (OpenRationalMayerVietoris.homologyFunctor n).map
  ext x
  rfl

/-- The first member of the actual pullback cover of the union. -/
abbrev leftSet (U V : Opens X) : Set ↥(U ⊔ V) :=
  (Subtype.val : ↥(U ⊔ V) → X) ⁻¹' (U : Set X)

/-- The second member of the actual pullback cover of the union. -/
abbrev rightSet (U V : Opens X) : Set ↥(U ⊔ V) :=
  (Subtype.val : ↥(U ⊔ V) → X) ⁻¹' (V : Set X)

theorem leftSet_isOpen (U V : Opens X) : IsOpen (leftSet U V) :=
  U.isOpen.preimage continuous_subtype_val

theorem rightSet_isOpen (U V : Opens X) : IsOpen (rightSet U V) :=
  V.isOpen.preimage continuous_subtype_val

theorem cover (U V : Opens X) : leftSet U V ∪ rightSet U V = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  exact x.property

/-- Canonical identification of the pulled-back intersection homology. -/
abbrev intersectionIso (U V : Opens X) (n : ℕ) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (TopCat.of ↥(leftSet U V ∩ rightSet U V))).homology n ≅
      openRationalHomology (U ⊓ V) n :=
  preimageHomologyIso (show U ⊓ V ≤ U ⊔ V from inf_le_left.trans le_sup_left) n

/-- Canonical identification of the two middle summands. -/
def middleIso (U V : Opens X) (n : ℕ) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (leftSet U V))).homology n ⊞
        (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (rightSet U V))).homology n ≅
      openRationalHomology U n ⊞ openRationalHomology V n :=
  biprod.mapIso (preimageHomologyIso (show U ≤ U ⊔ V from le_sup_left) n)
    (preimageHomologyIso (show V ≤ U ⊔ V from le_sup_right) n)

end OpenRationalMayerVietoris

open OAI.AlgebraicTopology.Duality.Poincare.OpenRational.OpenRationalMayerVietoris

/-- The actual pair of native inclusions with signs (+,-). -/
def openRationalMayerVietorisFirst (U V : Opens X) (n : ℕ) :
    openRationalHomology (U ⊓ V) n ⟶ openRationalHomology U n ⊞ openRationalHomology V n :=
  biprod.lift (openRationalHomologyMap (show U ⊓ V ≤ U from inf_le_left) n)
    (-openRationalHomologyMap (show U ⊓ V ≤ V from inf_le_right) n)

/-- The sum of the actual inclusion images in the native union. -/
def openRationalMayerVietorisSecond (U V : Opens X) (n : ℕ) :
    openRationalHomology U n ⊞ openRationalHomology V n ⟶ openRationalHomology (U ⊔ V) n :=
  biprod.desc (openRationalHomologyMap (show U ≤ U ⊔ V from le_sup_left) n)
    (openRationalHomologyMap (show V ≤ U ⊔ V from le_sup_right) n)

theorem openRationalMayerVietorisFirst_formula (U V : Opens X) (n : ℕ) :
    openRationalMayerVietorisFirst U V n =
      biprod.lift
        (Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ)
          (TopCat.ofHom (ContinuousMap.inclusion (show U ⊓ V ≤ U from inf_le_left))) n)
        (-Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ)
          (TopCat.ofHom (ContinuousMap.inclusion (show U ⊓ V ≤ V from inf_le_right))) n) := rfl

theorem openRationalMayerVietorisSecond_formula (U V : Opens X) (n : ℕ) :
    openRationalMayerVietorisSecond U V n =
      biprod.desc
        (Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ)
          (TopCat.ofHom (ContinuousMap.inclusion (show U ≤ U ⊔ V from le_sup_left))) n)
        (Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ)
          (TopCat.ofHom (ContinuousMap.inclusion (show V ≤ U ⊔ V from le_sup_right))) n) := rfl

/-- The actual boundary transported along the intersection homeomorphism. -/
def openRationalMayerVietorisBoundary (U V : Opens X) (n : ℕ) :
    openRationalHomology (U ⊔ V) (n + 1) ⟶ openRationalHomology (U ⊓ V) n :=
  RationalHomologyMayerVietoris.rationalMayerVietorisBoundary (TopCat.of ↥(U ⊔ V)) (OpenRationalMayerVietoris.leftSet U V) (OpenRationalMayerVietoris.rightSet U V)
    (OpenRationalMayerVietoris.leftSet_isOpen U V) (OpenRationalMayerVietoris.rightSet_isOpen U V) (OpenRationalMayerVietoris.cover U V) n ≫ (OpenRationalMayerVietoris.intersectionIso U V n).hom

namespace OpenRationalMayerVietoris

/-- The canonical homeomorphisms preserve the signed first map. -/
@[reassoc]
theorem first_comm (U V : Opens X) (n : ℕ) :
    RationalHomologyMayerVietoris.rationalMayerVietorisInclusion (TopCat.of ↥(U ⊔ V)) (leftSet U V) (rightSet U V) n ≫
        (middleIso U V n).hom =
      (intersectionIso U V n).hom ≫ openRationalMayerVietorisFirst U V n := by
  apply biprod.hom_ext
  · simpa [middleIso, openRationalMayerVietorisFirst, RationalHomologyMayerVietoris.rationalMayerVietorisInclusion_formula] using
      preimageHomologyIso_naturality
        (show U ⊓ V ≤ U from inf_le_left) (show U ≤ U ⊔ V from le_sup_left) n
  · simpa [middleIso, openRationalMayerVietorisFirst, RationalHomologyMayerVietoris.rationalMayerVietorisInclusion_formula] using
      congrArg Neg.neg (preimageHomologyIso_naturality
        (show U ⊓ V ≤ V from inf_le_right) (show V ≤ U ⊔ V from le_sup_right) n)

/-- The canonical homeomorphisms preserve the sum of inclusion images. -/
@[reassoc]
theorem second_comm (U V : Opens X) (n : ℕ) :
    RationalHomologyMayerVietoris.rationalMayerVietorisSum (TopCat.of ↥(U ⊔ V)) (leftSet U V) (rightSet U V) n =
      (middleIso U V n).hom ≫ openRationalMayerVietorisSecond U V n := by
  apply biprod.hom_ext'
  · simpa [middleIso, openRationalMayerVietorisSecond, RationalHomologyMayerVietoris.rationalMayerVietorisSum_formula] using
      (preimageHomologyIso_ambient (show U ≤ U ⊔ V from le_sup_left) n).symm
  · simpa [middleIso, openRationalMayerVietorisSecond, RationalHomologyMayerVietoris.rationalMayerVietorisSum_formula] using
      (preimageHomologyIso_ambient (show V ≤ U ⊔ V from le_sup_right) n).symm

end OpenRationalMayerVietoris

@[reassoc (attr := simp)]
theorem openRationalMayerVietorisFirst_second (U V : Opens X) (n : ℕ) :
    openRationalMayerVietorisFirst U V n ≫ openRationalMayerVietorisSecond U V n = 0 := by
  apply (cancel_epi (OpenRationalMayerVietoris.intersectionIso U V n).hom).1
  rw [← Category.assoc, ← OpenRationalMayerVietoris.first_comm, Category.assoc, ← OpenRationalMayerVietoris.second_comm,
    RationalHomologyMayerVietoris.rationalMayerVietorisInclusion_sum, comp_zero]

@[reassoc (attr := simp)]
theorem openRationalMayerVietorisSecond_boundary (U V : Opens X) (n : ℕ) :
    openRationalMayerVietorisSecond U V (n + 1) ≫ openRationalMayerVietorisBoundary U V n = 0 := by
  apply (cancel_epi (OpenRationalMayerVietoris.middleIso U V (n + 1)).hom).1
  rw [← Category.assoc, ← OpenRationalMayerVietoris.second_comm, openRationalMayerVietorisBoundary,
    ← Category.assoc, RationalHomologyMayerVietoris.rationalMayerVietorisSum_boundary, zero_comp, comp_zero]

@[reassoc (attr := simp)]
theorem openRationalMayerVietorisBoundary_first (U V : Opens X) (n : ℕ) :
    openRationalMayerVietorisBoundary U V n ≫ openRationalMayerVietorisFirst U V n = 0 := by
  rw [openRationalMayerVietorisBoundary, Category.assoc, ← OpenRationalMayerVietoris.first_comm,
    ← Category.assoc, RationalHomologyMayerVietoris.rationalMayerVietorisBoundary_inclusion, zero_comp]

/-- Exactness at the sum of homologies of the two native opens. -/
theorem openRationalMayerVietoris_exact_middle (U V : Opens X) (n : ℕ) :
    (ShortComplex.mk (openRationalMayerVietorisFirst U V n)
      (openRationalMayerVietorisSecond U V n) (openRationalMayerVietorisFirst_second U V n)).Exact := by
  let S := ShortComplex.mk
    (RationalHomologyMayerVietoris.rationalMayerVietorisInclusion (TopCat.of ↥(U ⊔ V)) (OpenRationalMayerVietoris.leftSet U V) (OpenRationalMayerVietoris.rightSet U V) n)
    (RationalHomologyMayerVietoris.rationalMayerVietorisSum (TopCat.of ↥(U ⊔ V)) (OpenRationalMayerVietoris.leftSet U V) (OpenRationalMayerVietoris.rightSet U V) n)
    (RationalHomologyMayerVietoris.rationalMayerVietorisInclusion_sum _ _ _ _)
  refine ShortComplex.exact_of_iso (S₁ := S) ?_
    (RationalHomologyMayerVietoris.rationalMayerVietoris_exact_middle _ _ _ (OpenRationalMayerVietoris.leftSet_isOpen U V)
      (OpenRationalMayerVietoris.rightSet_isOpen U V) (OpenRationalMayerVietoris.cover U V) n)
  refine ShortComplex.isoMk (OpenRationalMayerVietoris.intersectionIso U V n) (OpenRationalMayerVietoris.middleIso U V n) (Iso.refl _) ?_ ?_
  · exact (OpenRationalMayerVietoris.first_comm U V n).symm
  · simpa [S] using (OpenRationalMayerVietoris.second_comm U V n).symm

/-- Exactness at positive-degree ordinary homology of the native union. -/
theorem openRationalMayerVietoris_exact_union (U V : Opens X) (n : ℕ) :
    (ShortComplex.mk (openRationalMayerVietorisSecond U V (n + 1))
      (openRationalMayerVietorisBoundary U V n)
      (openRationalMayerVietorisSecond_boundary U V n)).Exact := by
  let S := ShortComplex.mk
    (RationalHomologyMayerVietoris.rationalMayerVietorisSum (TopCat.of ↥(U ⊔ V)) (OpenRationalMayerVietoris.leftSet U V) (OpenRationalMayerVietoris.rightSet U V) (n + 1))
    (RationalHomologyMayerVietoris.rationalMayerVietorisBoundary (TopCat.of ↥(U ⊔ V)) (OpenRationalMayerVietoris.leftSet U V) (OpenRationalMayerVietoris.rightSet U V)
      (OpenRationalMayerVietoris.leftSet_isOpen U V) (OpenRationalMayerVietoris.rightSet_isOpen U V) (OpenRationalMayerVietoris.cover U V) n)
    (RationalHomologyMayerVietoris.rationalMayerVietorisSum_boundary _ _ _ _ _ _ _)
  refine ShortComplex.exact_of_iso (S₁ := S) ?_
    (RationalHomologyMayerVietoris.rationalMayerVietoris_exact_ambient _ _ _ (OpenRationalMayerVietoris.leftSet_isOpen U V)
      (OpenRationalMayerVietoris.rightSet_isOpen U V) (OpenRationalMayerVietoris.cover U V) n)
  refine ShortComplex.isoMk (OpenRationalMayerVietoris.middleIso U V (n + 1)) (Iso.refl _) (OpenRationalMayerVietoris.intersectionIso U V n) ?_ ?_
  · simpa [S] using (OpenRationalMayerVietoris.second_comm U V (n + 1)).symm
  · simp [S, openRationalMayerVietorisBoundary]

/-- Exactness at ordinary homology of the native intersection. -/
theorem openRationalMayerVietoris_exact_intersection (U V : Opens X) (n : ℕ) :
    (ShortComplex.mk (openRationalMayerVietorisBoundary U V n)
      (openRationalMayerVietorisFirst U V n)
      (openRationalMayerVietorisBoundary_first U V n)).Exact := by
  let S := ShortComplex.mk
    (RationalHomologyMayerVietoris.rationalMayerVietorisBoundary (TopCat.of ↥(U ⊔ V)) (OpenRationalMayerVietoris.leftSet U V) (OpenRationalMayerVietoris.rightSet U V)
      (OpenRationalMayerVietoris.leftSet_isOpen U V) (OpenRationalMayerVietoris.rightSet_isOpen U V) (OpenRationalMayerVietoris.cover U V) n)
    (RationalHomologyMayerVietoris.rationalMayerVietorisInclusion (TopCat.of ↥(U ⊔ V)) (OpenRationalMayerVietoris.leftSet U V) (OpenRationalMayerVietoris.rightSet U V) n)
    (RationalHomologyMayerVietoris.rationalMayerVietorisBoundary_inclusion _ _ _ _ _ _ _)
  refine ShortComplex.exact_of_iso (S₁ := S) ?_
    (RationalHomologyMayerVietoris.rationalMayerVietoris_exact_intersection _ _ _ (OpenRationalMayerVietoris.leftSet_isOpen U V)
      (OpenRationalMayerVietoris.rightSet_isOpen U V) (OpenRationalMayerVietoris.cover U V) n)
  refine ShortComplex.isoMk (Iso.refl _) (OpenRationalMayerVietoris.intersectionIso U V n) (OpenRationalMayerVietoris.middleIso U V n) ?_ ?_
  · simp [S, openRationalMayerVietorisBoundary]
  · exact (OpenRationalMayerVietoris.first_comm U V n).symm

/-- Six consecutive native-open ordinary rational homology terms. -/
def openRationalMayerVietorisSequence (U V : Opens X) (n : ℕ) :
    ComposableArrows (ModuleCat.{0} ℚ) 5 :=
  ComposableArrows.mk₅ (openRationalMayerVietorisFirst U V (n + 1))
    (openRationalMayerVietorisSecond U V (n + 1)) (openRationalMayerVietorisBoundary U V n)
    (openRationalMayerVietorisFirst U V n) (openRationalMayerVietorisSecond U V n)

/-- The actual native-open rational Mayer--Vietoris sequence is exact. -/
theorem openRationalMayerVietorisSequence_exact (U V : Opens X) (n : ℕ) :
    (openRationalMayerVietorisSequence U V n).Exact :=
  ComposableArrows.exact_of_δ₀ (openRationalMayerVietoris_exact_middle U V (n + 1)).exact_toComposableArrows
    (ComposableArrows.exact_of_δ₀ (openRationalMayerVietoris_exact_union U V n).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀ (openRationalMayerVietoris_exact_intersection U V n).exact_toComposableArrows
        (openRationalMayerVietoris_exact_middle U V n).exact_toComposableArrows))

/-- The sequence ends with a surjection onto degree-zero union homology. -/
theorem openRationalMayerVietorisSecond_zero_epi (U V : Opens X) :
    Epi (openRationalMayerVietorisSecond U V 0) := by
  have : Epi (RationalHomologyMayerVietoris.rationalMayerVietorisSum (TopCat.of ↥(U ⊔ V)) (OpenRationalMayerVietoris.leftSet U V) (OpenRationalMayerVietoris.rightSet U V) 0) :=
    RationalHomologyMayerVietoris.rationalMayerVietorisSum_zero_epi _ _ _ (OpenRationalMayerVietoris.leftSet_isOpen U V) (OpenRationalMayerVietoris.rightSet_isOpen U V) (OpenRationalMayerVietoris.cover U V)
  exact epi_of_epi_fac (OpenRationalMayerVietoris.second_comm U V 0).symm

theorem openRationalMayerVietorisSecond_zero_surjective (U V : Opens X) :
    Function.Surjective (openRationalMayerVietorisSecond U V 0) :=
  (ModuleCat.epi_iff_surjective _).mp (openRationalMayerVietorisSecond_zero_epi U V)

end

end OAI.AlgebraicTopology.Duality.Poincare.OpenRational
