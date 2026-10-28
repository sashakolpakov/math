import OAI.AlgebraicTopology.Duality.Poincare.CapConnecting
import OAI.AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris

/-! # Cap Mayer Vietoris Connecting -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CapMayerVietorisConnecting

noncomputable section

/-!
# Concrete local-chain lifts for cap Mayer--Vietoris compatibility

This module expresses the native ordinary Mayer--Vietoris boundary using
actual chains on the two opens and their common boundary on the intersection.
It supplies the endpoint transport used by the supported-cap construction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Two local chains as an element of the actual middle complex in the
rational Mayer--Vietoris sequence. -/
def rationalMayerVietorisPair (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (u : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X n)
    (v : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).X n) :
    (RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence X U V).X₂.X n :=
  (biprod.inl : Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U) ⟶
    Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U) ⊞
      Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).f n u +
  (biprod.inr : Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V) ⟶
    Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U) ⊞
      Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).f n v

/-- The native sum map on a pair is the sum of the actual small-chain inclusions. -/
theorem rationalMayerVietorisPair_sum (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (u : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X n)
    (v : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).X n) :
    (RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence X U V).g.f n
        (rationalMayerVietorisPair X U V n u v) =
      (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft X U V)).f n u +
      (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X U V)).f n v := by
  have hu := ConcreteCategory.congr_hom
    (HomologicalComplex.biprod_inl_desc_f
      (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft X U V))
      (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X U V)) n) u
  have hv := ConcreteCategory.congr_hom
    (HomologicalComplex.biprod_inr_desc_f
      (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft X U V))
      (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X U V)) n) v
  unfold rationalMayerVietorisPair
  rw [map_add]
  exact congrArg₂ (· + ·) hu hv

/-- The first native map is the local pair with the conventional opposite
sign on its second component. -/
theorem rationalMayerVietorisPair_first (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (a : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∩ V : Set X))).X n) :
    (RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence X U V).f.f n a =
      rationalMayerVietorisPair X U V n
        ((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
          (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U))).f n a)
        (-((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
          (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V))).f n a)) := by
  simp [rationalMayerVietorisPair, RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence_f, biprod.lift_eq,
    HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
    HomologicalComplex.neg_f_apply]
  rfl

/-- Differentiating the actual middle-complex pair differentiates its two chains. -/
theorem rationalMayerVietorisPair_boundary (X : TopCat.{0}) (U V : Set X) (i j : ℕ)
    (u : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X i)
    (v : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).X i) :
    (RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence X U V).X₂.d i j
        (rationalMayerVietorisPair X U V i u v) =
      rationalMayerVietorisPair X U V j
        ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d i j u)
        ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).d i j v) := by
  have hu := ConcreteCategory.congr_hom
    ((biprod.inl : Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U) ⟶
      Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U) ⊞
        Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).comm i j) u
  have hv := ConcreteCategory.congr_hom
    ((biprod.inr : Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V) ⟶
      Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U) ⊞
        Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).comm i j) v
  unfold rationalMayerVietorisPair
  rw [map_add]
  exact congrArg₂ (· + ·) hu hv

/-- Compute the actual ordinary Mayer--Vietoris connecting class from local
chains with the prescribed common boundary on the intersection. -/
theorem rationalMayerVietorisBoundary_eq_of_components
    (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (RationalHomologyMayerVietoris.binarySmallRationalChains X U V) (n + 1))
    (u : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X (n + 1))
    (v : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).X (n + 1))
    (a : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∩ V : Set X))) n)
    (hz : (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft X U V)).f (n + 1) u +
      (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X U V)).f (n + 1) v = z.val)
    (hu : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d (n + 1) n u =
      (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U))).f n a.val)
    (hv : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).d (n + 1) n v =
      -((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V))).f n a.val)) :
    RationalHomologyMayerVietoris.rationalMayerVietorisBoundary X U V hU hV hcover n
      (HomologicalComplex.homologyMap (RationalHomologyMayerVietoris.binarySmallRationalChainInclusion X U V) (n + 1)
        (Cohomology.Singular.ChainRepresentatives.chainClass (RationalHomologyMayerVietoris.binarySmallRationalChains X U V) (n + 1) z)) =
      Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∩ V : Set X))) n a := by
  apply RationalHomologyMayerVietoris.rationalMayerVietorisBoundary_eq_of_lift X U V hU hV hcover n z
    (rationalMayerVietorisPair X U V (n + 1) u v) a
  · rw [rationalMayerVietorisPair_sum]
    exact hz
  · rw [rationalMayerVietorisPair_boundary, hu, hv, rationalMayerVietorisPair_first]

/-- The component formula with the precise sign supplied by the cap
boundary law for a degree-`p` cochain. -/
theorem rationalMayerVietorisBoundary_eq_of_signed_components
    (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (p n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (RationalHomologyMayerVietoris.binarySmallRationalChains X U V) (n + 1))
    (u : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X (n + 1))
    (v : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).X (n + 1))
    (a : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∩ V : Set X))) n)
    (hz : (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft X U V)).f (n + 1) u +
      (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X U V)).f (n + 1) v = z.val)
    (hu : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d (n + 1) n u =
      ((-1 : ℤ) ^ (p + 1)) • (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U))).f n a.val)
    (hv : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).d (n + 1) n v =
      - (((-1 : ℤ) ^ (p + 1)) • (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V))).f n a.val)) :
    RationalHomologyMayerVietoris.rationalMayerVietorisBoundary X U V hU hV hcover n
      (HomologicalComplex.homologyMap (RationalHomologyMayerVietoris.binarySmallRationalChainInclusion X U V) (n + 1)
        (Cohomology.Singular.ChainRepresentatives.chainClass (RationalHomologyMayerVietoris.binarySmallRationalChains X U V) (n + 1) z)) =
      ((-1 : ℤ) ^ (p + 1)) •
        Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∩ V : Set X))) n a := by
  have hval : (((-1 : ℤ) ^ (p + 1)) • a :
      Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∩ V : Set X))) n).val =
      ((-1 : ℤ) ^ (p + 1)) • a.val :=
    map_zsmul (Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∩ V : Set X))) n).subtype
      ((-1 : ℤ) ^ (p + 1)) a
  have h := rationalMayerVietorisBoundary_eq_of_components X U V hU hV hcover n
    z u v (((-1 : ℤ) ^ (p + 1)) • a) hz
    (by rw [hval, map_zsmul]; exact hu)
    (by rw [hval, map_zsmul]; exact hv)
  simpa only [map_zsmul] using h

end

end OAI.AlgebraicTopology.Duality.Poincare.CapMayerVietorisConnecting
