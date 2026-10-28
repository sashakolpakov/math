import OAI.AlgebraicTopology.Duality.Poincare.OpenRational
import OAI.AlgebraicTopology.Duality.Poincare.CapMayerVietorisConnecting
import OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallUnion

/-! # Open Mayer Vietoris Components -/

namespace OAI.AlgebraicTopology.Duality.Poincare.OpenMayerVietorisComponents

noncomputable section

/-!
# Native open Mayer--Vietoris from actual local chains

The connecting map for two opens is computed using chains in the opens and
their common boundary in the intersection. Their union need not exhaust the
original ambient space. The proof uses the genuine pullback cover inside the
union and the actual flattening homeomorphisms.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallUnion.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace OpenRationalMayerVietoris

variable {X : TopCat.{0}}

/-- The actual rational chain isomorphism which flattens a pullback open. -/
def preimageChainIso {U W : Opens X} (h : U ≤ W) :
    Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
        (TopCat.of ((Subtype.val : W → X) ⁻¹' (U : Set X))) ≅
      Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U) :=
  (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).mapIso (TopCat.isoOfHomeo (OpenRational.OpenRationalMayerVietoris.preimageHomeomorph h))

/-- Its homology map is exactly the native-open comparison already used
in the definition of the Mayer--Vietoris boundary. -/
theorem preimageChainIso_homology {U W : Opens X} (h : U ≤ W) (n : ℕ) :
    HomologicalComplex.homologyMap (preimageChainIso h).hom n =
      (OpenRational.OpenRationalMayerVietoris.preimageHomologyIso h n).hom := rfl

/-- Flattening the pullback commutes with its actual chain inclusion. -/
@[reassoc]
theorem preimageChainIso_naturality {U V W : Opens X}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion (TopCat.of W)
          (show (Subtype.val : W → X) ⁻¹' (U : Set X) ⊆
            (Subtype.val : W → X) ⁻¹' (V : Set X) from fun _ hx => hUV hx)) ≫
        (preimageChainIso hVW).hom =
      (preimageChainIso (hUV.trans hVW)).hom ≫
        Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (TopCat.ofHom (ContinuousMap.inclusion hUV)) := by
  change (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map _ ≫ (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map _ =
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map _ ≫ (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
  ext x
  rfl

/-- Flattening followed by native inclusion is the pullback inclusion. -/
@[reassoc]
theorem preimageChainIso_ambient {U W : Opens X} (h : U ≤ W) :
    (preimageChainIso h).hom ≫
        Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (TopCat.ofHom (ContinuousMap.inclusion h)) =
      Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of W) ((Subtype.val : W → X) ⁻¹' (U : Set X))) := by
  change (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map _ ≫ (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map _ =
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map _
  rw [← Functor.map_comp]
  apply congrArg (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
  ext x
  rfl

/-- The inverse chain comparison commutes with literal nested inclusions. -/
@[reassoc]
theorem preimageChainIso_inv_naturality {U V W : Opens X}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    (preimageChainIso (hUV.trans hVW)).inv ≫
        Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
          (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion (TopCat.of W)
            (show (Subtype.val : W → X) ⁻¹' (U : Set X) ⊆
              (Subtype.val : W → X) ⁻¹' (V : Set X) from fun _ hx => hUV hx)) =
      Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (TopCat.ofHom (ContinuousMap.inclusion hUV)) ≫
        (preimageChainIso hVW).inv := by
  apply (cancel_mono (preimageChainIso hVW).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (fun f => (preimageChainIso (hUV.trans hVW)).inv ≫ f)
      (preimageChainIso_naturality hUV hVW)

/-- Lifting into the pullback and then including in the larger open is
the original native open inclusion. -/
@[reassoc]
theorem preimageChainIso_inv_ambient {U W : Opens X} (h : U ≤ W) :
    (preimageChainIso h).inv ≫
        Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of W) ((Subtype.val : W → X) ⁻¹' (U : Set X))) =
      Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (TopCat.ofHom (ContinuousMap.inclusion h)) := by
  rw [← preimageChainIso_ambient h, Iso.inv_hom_id_assoc]

end OpenRationalMayerVietoris

/-- A middle chain whose boundary lies in the first term maps to an
actual cycle in the third term of a short complex. -/
def smallCycleOfMiddleBoundary
    (S : ShortComplex (ChainComplex (ModuleCat.{0} ℚ) ℕ)) (n : ℕ)
    (b : S.X₂.X (n + 1)) (a : S.X₁.X n)
    (h : S.f.f n a = S.X₂.d (n + 1) n b) : Cohomology.Singular.ChainRepresentatives.chainCycles S.X₃ (n + 1) := by
  refine ⟨S.g.f (n + 1) b, ?_⟩
  apply (Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ S.X₃ n _).mpr
  have hc := ConcreteCategory.congr_hom (S.g.comm (n + 1) n) b
  have hz := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom S.zero n) a
  change S.X₃.d (n + 1) n (S.g.f (n + 1) b) =
    S.g.f n (S.X₂.d (n + 1) n b) at hc
  change S.g.f n (S.f.f n a) = 0 at hz
  exact hc.trans ((congrArg (S.g.f n) h.symm).trans hz)

/-- The native middle-chain pair has the prescribed signed common boundary. -/
theorem rationalMayerVietorisPair_boundary_signed
    (X : TopCat.{0}) (U V : Set X) (s : ℤ) (n : ℕ)
    (u : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X (n + 1))
    (v : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).X (n + 1))
    (a : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∩ V : Set X))) n)
    (hu : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d (n + 1) n u =
      s • (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U))).f n a.val)
    (hv : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).d (n + 1) n v =
      -(s • (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V))).f n a.val)) :
    (RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence X U V).X₂.d (n + 1) n
        (CapMayerVietorisConnecting.rationalMayerVietorisPair X U V (n + 1) u v) =
      (RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence X U V).f.f n (s • a.val) := by
  rw [CapMayerVietorisConnecting.rationalMayerVietorisPair_boundary, hu, hv, CapMayerVietorisConnecting.rationalMayerVietorisPair_first]
  simp only [map_zsmul]

/-- Actual small cycle represented by a local pair with a signed common boundary. -/
def rationalMayerVietorisSmallCycle
    (X : TopCat.{0}) (U V : Set X) (s : ℤ) (n : ℕ)
    (u : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X (n + 1))
    (v : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).X (n + 1))
    (a : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∩ V : Set X))) n)
    (hu : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d (n + 1) n u =
      s • (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U))).f n a.val)
    (hv : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).d (n + 1) n v =
      -(s • (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V))).f n a.val)) :
    Cohomology.Singular.ChainRepresentatives.chainCycles (RationalHomologyMayerVietoris.binarySmallRationalChains X U V) (n + 1) :=
  smallCycleOfMiddleBoundary (RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence X U V) n
    (CapMayerVietorisConnecting.rationalMayerVietorisPair X U V (n + 1) u v) (s • a.val)
    (rationalMayerVietorisPair_boundary_signed X U V s n u v a hu hv).symm

@[simp]
theorem rationalMayerVietorisSmallCycle_val
    (X : TopCat.{0}) (U V : Set X) (s : ℤ) (n : ℕ)
    (u : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X (n + 1))
    (v : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).X (n + 1))
    (a : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∩ V : Set X))) n)
    (hu : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d (n + 1) n u =
      s • (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U))).f n a.val)
    (hv : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).d (n + 1) n v =
      -(s • (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V))).f n a.val)) :
    (rationalMayerVietorisSmallCycle X U V s n u v a hu hv).val =
      (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft X U V)).f (n + 1) u +
        (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X U V)).f (n + 1) v :=
  CapMayerVietorisConnecting.rationalMayerVietorisPair_sum X U V (n + 1) u v

/-- The native open-cover boundary is computed from actual local chains
with a signed common boundary. The two opens need not cover the ambient space. -/
theorem openRationalMayerVietorisBoundary_eq_of_signed_components
    {X : TopCat.{0}} (U V : Opens X) (p n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of ↥(U ⊔ V))) (n + 1))
    (u : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X (n + 1))
    (v : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).X (n + 1))
    (a : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of ↥(U ⊓ V))) n)
    (hz :
      (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (TopCat.ofHom (ContinuousMap.inclusion (show U ≤ U ⊔ V from le_sup_left)))).f (n + 1) u +
      (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (TopCat.ofHom (ContinuousMap.inclusion (show V ≤ U ⊔ V from le_sup_right)))).f (n + 1) v = z.val)
    (hu : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d (n + 1) n u =
      ((-1 : ℤ) ^ (p + 1)) •
        (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
          (TopCat.ofHom (ContinuousMap.inclusion (show U ⊓ V ≤ U from inf_le_left)))).f n a.val)
    (hv : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).d (n + 1) n v =
      - (((-1 : ℤ) ^ (p + 1)) •
        (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
          (TopCat.ofHom (ContinuousMap.inclusion (show U ⊓ V ≤ V from inf_le_right)))).f n a.val)) :
    OpenRational.openRationalMayerVietorisBoundary U V n
        (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of ↥(U ⊔ V))) (n + 1) z) =
      ((-1 : ℤ) ^ (p + 1)) •
        Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of ↥(U ⊓ V))) n a := by
  let W : TopCat.{0} := TopCat.of ↥(U ⊔ V)
  let U' : Set W := OpenRational.OpenRationalMayerVietoris.leftSet U V
  let V' : Set W := OpenRational.OpenRationalMayerVietoris.rightSet U V
  let eU := OpenRationalMayerVietoris.preimageChainIso (show U ≤ U ⊔ V from le_sup_left)
  let eV := OpenRationalMayerVietoris.preimageChainIso (show V ≤ U ⊔ V from le_sup_right)
  let eI := OpenRationalMayerVietoris.preimageChainIso (show U ⊓ V ≤ U ⊔ V from inf_le_left.trans le_sup_left)
  let u' := eU.inv.f (n + 1) u
  let v' := eV.inv.f (n + 1) v
  let a' : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U' ∩ V' : Set W))) n :=
    Cohomology.Singular.EvaluationNaturality.chainCycleMap eI.inv n a
  have hu' : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U')).d (n + 1) n u' =
      ((-1 : ℤ) ^ (p + 1)) •
        (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
          (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion W (Set.inter_subset_left : U' ∩ V' ⊆ U'))).f n a'.val := by
    have hc := ConcreteCategory.congr_hom (eU.inv.comm (n + 1) n) u
    have hi := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (OpenRationalMayerVietoris.preimageChainIso_inv_naturality
        (show U ⊓ V ≤ U from inf_le_left) (show U ≤ U ⊔ V from le_sup_left)) n) a.val
    change (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U')).d (n + 1) n u' =
      eU.inv.f n ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d (n + 1) n u) at hc
    change (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion W (Set.inter_subset_left : U' ∩ V' ⊆ U'))).f n a'.val =
      eU.inv.f n ((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (TopCat.ofHom (ContinuousMap.inclusion (show U ⊓ V ≤ U from inf_le_left)))).f n a.val) at hi
    rw [hc, hu, map_zsmul, ← hi]
  have hv' : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V')).d (n + 1) n v' =
      - (((-1 : ℤ) ^ (p + 1)) •
        (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
          (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion W (Set.inter_subset_right : U' ∩ V' ⊆ V'))).f n a'.val) := by
    have hc := ConcreteCategory.congr_hom (eV.inv.comm (n + 1) n) v
    have hi := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (OpenRationalMayerVietoris.preimageChainIso_inv_naturality
        (show U ⊓ V ≤ V from inf_le_right) (show V ≤ U ⊔ V from le_sup_right)) n) a.val
    change (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V')).d (n + 1) n v' =
      eV.inv.f n ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).d (n + 1) n v) at hc
    change (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion W (Set.inter_subset_right : U' ∩ V' ⊆ V'))).f n a'.val =
      eV.inv.f n ((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (TopCat.ofHom (ContinuousMap.inclusion (show U ⊓ V ≤ V from inf_le_right)))).f n a.val) at hi
    rw [hc, hv, map_neg, map_zsmul, ← hi]
  let z' := rationalMayerVietorisSmallCycle W U' V' ((-1 : ℤ) ^ (p + 1)) n u' v' a' hu' hv'
  have hz' : Cohomology.Singular.EvaluationNaturality.chainCycleMap (RationalHomologyMayerVietoris.binarySmallRationalChainInclusion W U' V') (n + 1) z' = z := by
    have hU := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (RationalHomologyMayerVietoris.binarySmallRationalChainInclusion_left W U' V') (n + 1)) u'
    have hV := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (RationalHomologyMayerVietoris.binarySmallRationalChainInclusion_right W U' V') (n + 1)) v'
    have hiU := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (OpenRationalMayerVietoris.preimageChainIso_inv_ambient (show U ≤ U ⊔ V from le_sup_left)) (n + 1)) u
    have hiV := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (OpenRationalMayerVietoris.preimageChainIso_inv_ambient (show V ≤ U ⊔ V from le_sup_right)) (n + 1)) v
    change (RationalHomologyMayerVietoris.binarySmallRationalChainInclusion W U' V').f (n + 1)
        ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft W U' V')).f (n + 1) u') =
      (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion W U')).f (n + 1) u' at hU
    change (RationalHomologyMayerVietoris.binarySmallRationalChainInclusion W U' V').f (n + 1)
        ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight W U' V')).f (n + 1) v') =
      (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion W V')).f (n + 1) v' at hV
    change (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion W U')).f (n + 1) u' =
      (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (TopCat.ofHom (ContinuousMap.inclusion (show U ≤ U ⊔ V from le_sup_left)))).f (n + 1) u at hiU
    change (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion W V')).f (n + 1) v' =
      (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (TopCat.ofHom (ContinuousMap.inclusion (show V ≤ U ⊔ V from le_sup_right)))).f (n + 1) v at hiV
    apply Subtype.ext
    change (RationalHomologyMayerVietoris.binarySmallRationalChainInclusion W U' V').f (n + 1) z'.val = z.val
    rw [rationalMayerVietorisSmallCycle_val, map_add, hU, hV, hiU, hiV]
    exact hz
  have hraw := CapMayerVietorisConnecting.rationalMayerVietorisBoundary_eq_of_signed_components W U' V'
    (OpenRational.OpenRationalMayerVietoris.leftSet_isOpen U V) (OpenRational.OpenRationalMayerVietoris.rightSet_isOpen U V) (OpenRational.OpenRationalMayerVietoris.cover U V) p n z' u' v' a'
    (rationalMayerVietorisSmallCycle_val W U' V' ((-1 : ℤ) ^ (p + 1)) n
      u' v' a' hu' hv').symm hu' hv'
  rw [Cohomology.Singular.EvaluationNaturality.chainClass_naturality, hz'] at hraw
  have ha : (OpenRational.OpenRationalMayerVietoris.intersectionIso U V n).hom
      (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U' ∩ V' : Set W))) n a') =
      Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of ↥(U ⊓ V))) n a := by
    change HomologicalComplex.homologyMap eI.hom n
      (Cohomology.Singular.ChainRepresentatives.chainClass _ n (Cohomology.Singular.EvaluationNaturality.chainCycleMap eI.inv n a)) = _
    rw [← Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
    change (HomologicalComplex.homologyMap eI.inv n ≫
      HomologicalComplex.homologyMap eI.hom n) (Cohomology.Singular.ChainRepresentatives.chainClass _ n a) = _
    rw [← HomologicalComplex.homologyMap_comp, eI.inv_hom_id,
      HomologicalComplex.homologyMap_id]
    rfl
  change (OpenRational.OpenRationalMayerVietoris.intersectionIso U V n).hom
    (RationalHomologyMayerVietoris.rationalMayerVietorisBoundary W U' V' (OpenRational.OpenRationalMayerVietoris.leftSet_isOpen U V)
      (OpenRational.OpenRationalMayerVietoris.rightSet_isOpen U V) (OpenRational.OpenRationalMayerVietoris.cover U V) n (Cohomology.Singular.ChainRepresentatives.chainClass _ (n + 1) z)) = _
  rw [hraw, map_zsmul, ha]

end

end OAI.AlgebraicTopology.Duality.Poincare.OpenMayerVietorisComponents
