import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental
import OAI.AlgebraicGeometry.CycleClass.Geometric.Point

/-! # Compact Manifold Fundamental -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles

noncomputable section

/-!
# The ordinary integral fundamental class of a compact complex manifold

The relative group supported on the whole manifold is identified with its
ordinary singular homology by the actual quotient by chains in the empty
subspace. Under this comparison the canonical compact-support class becomes
the unique ordinary class having the complex local generator at every point.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Relative chains supported on all of a space are ordinary chains. The
inverse of this isomorphism is the actual relative-chain projection. -/
def wholeSpaceSupportChainsIso (X : TopCat.{0}) :
    LocalHomology.Cycles.relativeSingularChains X (Set.univ : Set X)ᶜ ≅ LocalHomology.Cycles.integralSingularChains X := by
  letI : IsEmpty {x : X // x ∉ (Set.univ : Set X)} :=
    ⟨fun x => x.property (Set.mem_univ x.val)⟩
  have hzero : LocalHomology.Cycles.subspaceChainInclusion X (Set.univ : Set X)ᶜ = 0 :=
    (Point.Cycles.integralSingularChains_isZero_of_isEmpty
      (TopCat.of {x : X // x ∉ (Set.univ : Set X)})).eq_zero_of_src _
  letI : IsIso (LocalHomology.Cycles.relativeChainProjection X (Set.univ : Set X)ᶜ) :=
    cokernel.π_of_zero hzero
  exact (asIso (LocalHomology.Cycles.relativeChainProjection X (Set.univ : Set X)ᶜ)).symm

/-- The canonical whole-support comparison in actual integral homology. -/
def wholeSpaceSupportHomologyIso (X : TopCat.{0}) (n : ℕ) :
    HomologyWithSupports.Cycles.singularHomologyWithSupport X Set.univ n ≅ (LocalHomology.Cycles.integralSingularChains X).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapIso
    (wholeSpaceSupportChainsIso X)

@[simp]
theorem wholeSpaceSupportHomologyIso_inv (X : TopCat.{0}) (n : ℕ) :
    (wholeSpaceSupportHomologyIso X n).inv =
      HomologicalComplex.homologyMap (LocalHomology.Cycles.relativeChainProjection X (Set.univ : Set X)ᶜ) n := rfl

/-- The inverse whole-support comparison followed by local restriction
is exactly the ordinary projection to local homology. -/
@[reassoc]
theorem wholeSpaceSupportHomologyIso_inv_toPoint (X : TopCat.{0}) (n : ℕ) (x : X) :
    (wholeSpaceSupportHomologyIso X n).inv ≫
        LocalHomologyPresheaf.Cycles.localHomologyToPoint X Set.univ x (Set.mem_univ x) n =
      HomologicalComplex.homologyMap (LocalHomology.Cycles.relativeChainProjection X ({x}ᶜ : Set X)) n := by
  rw [wholeSpaceSupportHomologyIso_inv]
  unfold LocalHomologyPresheaf.Cycles.localHomologyToPoint
  rw [← HomologicalComplex.homologyMap_comp, LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint_projection]

/-- The forward comparison preserves the actual maps to local homology. -/
@[reassoc]
theorem wholeSpaceSupportHomologyIso_hom_toPoint (X : TopCat.{0}) (n : ℕ) (x : X) :
    (wholeSpaceSupportHomologyIso X n).hom ≫
        HomologicalComplex.homologyMap (LocalHomology.Cycles.relativeChainProjection X ({x}ᶜ : Set X)) n =
      LocalHomologyPresheaf.Cycles.localHomologyToPoint X Set.univ x (Set.mem_univ x) n := by
  apply (cancel_epi (wholeSpaceSupportHomologyIso X n).inv).mp
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    wholeSpaceSupportHomologyIso_inv_toPoint]

variable (p : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace (Fin p → ℂ) M] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M]

/-- The canonical integral fundamental class in ordinary singular
homology of a compact complex manifold. -/
def complexManifoldFundamentalClass : (LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology (2 * p) :=
  (wholeSpaceSupportHomologyIso (TopCat.of M) (2 * p)).hom
    (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (Set.univ : Set M) isCompact_univ)

/-- The ordinary fundamental class restricts to the complex generator by
the genuine projection from absolute to local singular homology. -/
theorem complexManifoldFundamentalClass_atPoint (x : M) :
    HomologicalComplex.homologyMap
        (LocalHomology.Cycles.relativeChainProjection (TopCat.of M) ({x}ᶜ : Set M)) (2 * p)
        (complexManifoldFundamentalClass p M) =
      ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x := by
  change ((wholeSpaceSupportHomologyIso (TopCat.of M) (2 * p)).hom ≫
    HomologicalComplex.homologyMap
      (LocalHomology.Cycles.relativeChainProjection (TopCat.of M) ({x}ᶜ : Set M)) (2 * p))
      (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (Set.univ : Set M) isCompact_univ) = _
  rw [wholeSpaceSupportHomologyIso_hom_toPoint]
  exact ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_atPoint p Set.univ isCompact_univ x (Set.mem_univ x)

/-- The ordinary class is unique with its prescribed complex local values. -/
theorem complexManifoldFundamentalClass_unique
    (a : (LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology (2 * p))
    (ha : ∀ x : M, HomologicalComplex.homologyMap
      (LocalHomology.Cycles.relativeChainProjection (TopCat.of M) ({x}ᶜ : Set M)) (2 * p) a =
        ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x) :
    a = complexManifoldFundamentalClass p M := by
  let q := wholeSpaceSupportHomologyIso (TopCat.of M) (2 * p)
  apply q.toLinearEquiv.symm.injective
  change q.inv a = q.inv (q.hom
    (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (Set.univ : Set M) isCompact_univ))
  rw [show q.inv (q.hom (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (Set.univ : Set M) isCompact_univ)) =
      ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (Set.univ : Set M) isCompact_univ from
        q.toLinearEquiv.symm_apply_apply _]
  apply ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_unique p Set.univ isCompact_univ
  intro x _
  exact (ConcreteCategory.congr_hom
    (wholeSpaceSupportHomologyIso_inv_toPoint (TopCat.of M) (2 * p) x) a).trans (ha x)

/-- The standard fundamental-class existence and uniqueness statement,
formulated in ordinary integral singular homology. -/
theorem existsUnique_complexManifoldFundamentalClass :
    ∃! a : (LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology (2 * p),
      ∀ x : M, HomologicalComplex.homologyMap
        (LocalHomology.Cycles.relativeChainProjection (TopCat.of M) ({x}ᶜ : Set M)) (2 * p) a =
          ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x :=
  ⟨complexManifoldFundamentalClass p M, complexManifoldFundamentalClass_atPoint p M,
    complexManifoldFundamentalClass_unique p M⟩

/-- A nonempty compact complex manifold has nonzero integral fundamental
class, since its actual restriction at any point is nonzero. -/
theorem complexManifoldFundamentalClass_ne_zero [Nonempty M] :
    complexManifoldFundamentalClass p M ≠ 0 := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty M›
  have hx := complexManifoldFundamentalClass_atPoint p M x
  rw [h, map_zero] at hx
  exact ComplexChartOrientation.Cycles.complexCanonicalLocalClass_ne_zero x hx.symm

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles
