import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldCap
import OAI.AlgebraicTopology.Duality.Poincare.MixedCapHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental

/-! # Compact Meaning -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactMeaning

noncomputable section

/-!
# The ordinary meaning of the compact-manifold cap map

For a compact complex manifold, the cap map constructed by passage through
compact supports is the ordinary singular cap product with the canonical
integral fundamental class. The comparison on cohomology is the already
proved map that forgets compact support.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false

/-- Projecting an ordinary homology class to relative homology commutes
with the actual relative cap product. -/
theorem relativeCapHomology_projection (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology (p + q)) :
    SupportRelativeCap.relativeCapHomology X A p q c
        (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) (p + q) z) =
      MixedCapHomology.mixedSingularCapHomology X p q
        (Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A p c) z := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p c
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) (p + q) z
  change SupportRelativeCap.relativeCapHomology X A p q (Cohomology.Singular.Representatives.cochainClass _ p c)
      (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) (p + q)
        (Cohomology.Singular.ChainRepresentatives.chainClass _ (p + q) z)) =
    MixedCapHomology.mixedSingularCapHomology X p q
      (HomologicalComplex.homologyMap (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A) p
        (Cohomology.Singular.Representatives.cochainClass _ p c)) (Cohomology.Singular.ChainRepresentatives.chainClass _ (p + q) z)
  rw [Cohomology.Singular.EvaluationNaturality.chainClass_naturality, SupportRelativeCap.relativeCapHomology_class_class, Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  change _ = MixedCapHomology.mixedSingularCapHomology X p q
    (Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X p
      (Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A) p c))
    (Cohomology.Singular.ChainRepresentatives.chainClass _ (p + q) z)
  rw [MixedCapHomology.mixedSingularCapHomology_class_class]
  apply congrArg (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) q)
  apply Subtype.ext
  exact SupportRelativeCap.relativeCap_projection X A p q c.val z.val

variable (n : ℕ) {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace (Fin n → ℂ) M] [IsManifold 𝓘(ℂ, Fin n → ℂ) 1 M]

/-- The canonical ordinary integral fundamental class, transported only
along an equality of homological degrees. -/
def complexFundamentalClassInDegree (d : ℕ) (hd : d = 2 * n) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology d :=
  (eqToHom (congrArg (fun j => (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology j) hd.symm))
    (AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass n M)

@[simp]
theorem complexFundamentalClassInDegree_top :
    complexFundamentalClassInDegree n (M := M) (2 * n) rfl =
      AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass n M := rfl

/-- The ordinary fundamental class projects to the same whole-support
orientation class used to define the compact-support cap. -/
theorem complexFundamentalClassInDegree_projection (d : ℕ) (hd : d = 2 * n) :
    HomologicalComplex.homologyMap
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) (Set.univ : Set M)ᶜ) d
        (complexFundamentalClassInDegree n (M := M) d hd) =
      ComplexManifoldCap.complexCompactClassInDegree n d hd (⊤ : TopologicalSpace.Compacts M) := by
  subst d
  change (AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles.wholeSpaceSupportHomologyIso (TopCat.of M) (2 * n)).inv
    ((AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles.wholeSpaceSupportHomologyIso (TopCat.of M) (2 * n)).hom
      (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass n (Set.univ : Set M) isCompact_univ)) = _
  exact ConcreteCategory.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles.wholeSpaceSupportHomologyIso (TopCat.of M) (2 * n)).hom_inv_id
    (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass n (Set.univ : Set M) isCompact_univ)

/-- Ordinary rational cohomology capped with the canonical ordinary
integral fundamental class, using the proved integral-to-rational map. -/
def complexManifoldOrdinaryCap (p q : ℕ) (hpq : p + q = 2 * n) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p ⟶
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of M)).homology q :=
  ModuleCat.ofHom {
    toFun := fun c => MixedCapHomology.mixedSingularCapHomology (TopCat.of M) p q c
      (complexFundamentalClassInDegree n (M := M) (p + q) hpq)
    map_add' := fun c d => by simp only [map_add, LinearMap.add_apply]
    map_smul' := fun r c => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }

@[simp]
theorem complexManifoldOrdinaryCap_apply (p q : ℕ) (hpq : p + q = 2 * n)
    (c : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :
    complexManifoldOrdinaryCap n (M := M) p q hpq c =
      MixedCapHomology.mixedSingularCapHomology (TopCat.of M) p q c
        (complexFundamentalClassInDegree n (M := M) (p + q) hpq) := rfl

/-- Forgetting compact support identifies the constructed cap map with
ordinary cap by the canonical fundamental class. -/
@[reassoc]
theorem compactSupportCap_eq_ordinaryCap (p q : ℕ) (hpq : p + q = 2 * n) :
    (CompactSupportCohomology.compactSupportedCohomologyIso (ModuleCat.of ℚ ℚ) (TopCat.of M) p).hom ≫
        complexManifoldOrdinaryCap n (M := M) p q hpq =
      ComplexManifoldCap.complexManifoldCompactSupportCap n (M := M) p q hpq := by
  let stage := CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M)
    (⊤ : TopologicalSpace.Compacts M) p
  have : IsIso stage := by
    have := CompactSupportCohomology.compactSupportCochainι_top_isIso (ModuleCat.of ℚ ℚ) (TopCat.of M)
    exact ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) p).mapIso
      (asIso (CompactSupportCohomology.compactSupportCochainι (ModuleCat.of ℚ ℚ) (TopCat.of M) ⊤))).isIso_hom
  apply (cancel_epi stage).mp
  calc
    stage ≫ ((CompactSupportCohomology.compactSupportedCohomologyIso (ModuleCat.of ℚ ℚ) (TopCat.of M) p).hom ≫
        complexManifoldOrdinaryCap n (M := M) p q hpq) =
      Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of M)
        (Set.univ : Set M)ᶜ p ≫ complexManifoldOrdinaryCap n (M := M) p q hpq := by
          rw [← Category.assoc, CompactSupportCohomology.compactSupportedCohomologyIso_hom]
          change (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) ⊤ p ≫
            CompactSupportCohomology.compactSupportedCohomologyForget (ModuleCat.of ℚ ℚ) (TopCat.of M) p) ≫ _ = _
          rw [CompactSupportCohomology.compactSupportCohomologyι_forget]
          simp only [TopologicalSpace.Compacts.coe_top]
    _ = SupportCapNaturality.relativeCapWithClass (TopCat.of M) (Set.univ : Set M)ᶜ p q
        (ComplexManifoldCap.complexCompactClassInDegree n (p + q) hpq ⊤) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change MixedCapHomology.mixedSingularCapHomology (TopCat.of M) p q
          (Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of M)
            (Set.univ : Set M)ᶜ p c)
          (complexFundamentalClassInDegree n (M := M) (p + q) hpq) =
        SupportRelativeCap.relativeCapHomology (TopCat.of M) (Set.univ : Set M)ᶜ p q c
          (ComplexManifoldCap.complexCompactClassInDegree n (p + q) hpq ⊤)
      rw [← complexFundamentalClassInDegree_projection n (p + q) hpq]
      exact (relativeCapHomology_projection _ _ p q c _).symm
    _ = stage ≫ ComplexManifoldCap.complexManifoldCompactSupportCap n (M := M) p q hpq :=
      (ComplexManifoldCap.complexManifoldCompactSupportCap_stage n p q hpq ⊤).symm

/-- The inverse compact-support comparison gives the exact same ordinary
cap map, rather than merely an abstract isomorphism of groups. -/
@[reassoc]
theorem ordinaryCap_eq_compactSupportCap (p q : ℕ) (hpq : p + q = 2 * n) :
    (CompactSupportCohomology.compactSupportedCohomologyIso (ModuleCat.of ℚ ℚ) (TopCat.of M) p).inv ≫
        ComplexManifoldCap.complexManifoldCompactSupportCap n (M := M) p q hpq =
      complexManifoldOrdinaryCap n (M := M) p q hpq := by
  rw [← compactSupportCap_eq_ordinaryCap n p q hpq, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactMeaning
