import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteExhaustion

/-! # Complex Locally Finite Fundamental -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles

noncomputable section

/-!
# The canonical locally finite fundamental class of a complex manifold

The canonical classes on compact supports are lifted through the actual
relative-chain exhaustion. The next-degree homology vanishing is proved
from the manifold dimension, so no inverse-limit or coherence hypothesis
is assumed. The resulting class has the canonical complex value at every
point and is uniquely determined by these values.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Compatibility of actual locally finite compact restriction with the
standard restriction between relative groups with supports. -/
@[reassoc]
theorem locallyFiniteCompactHomologyRestriction_supportRestriction (X : TopCat.{0})
    {K L : Set X} (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L) (n : ℕ) :
    LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction X L hL n ≫
      CompactSupportAssembly.Cycles.homologyWithSupportRestriction X hKL n =
        LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction X K hK n :=
  LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction_subset X hK hL hKL n

/-- Restricting first to a compact support and then to a point is the
actual locally finite restriction to that point. -/
@[reassoc]
theorem locallyFiniteCompactHomologyRestriction_toPoint (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) (x : X) (hx : x ∈ K) (n : ℕ) :
    LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction X K hK n ≫ LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n =
      LocallyFiniteCompactRestriction.Cycles.locallyFinitePointHomologyRestriction X x n :=
  LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction_subset X isCompact_singleton hK
    (singleton_subset_iff.mpr hx) n

theorem locallyFiniteCompactHomologyRestriction_toPoint_apply (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) (x : X) (hx : x ∈ K) (n : ℕ)
    (a : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology n) :
    LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n (LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction X K hK n a) =
      LocallyFiniteCompactRestriction.Cycles.locallyFinitePointHomologyRestriction X x n a :=
  ConcreteCategory.congr_hom (locallyFiniteCompactHomologyRestriction_toPoint X K hK x hx n) a

variable (p : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin p → ℂ) M]

/-- The next relative-homology degree along every compact exhaustion
vanishes by the proved manifold dimension bound. -/
theorem complexExhaustion_nextHomology_isZero (E : CompactExhaustion M) (i : ℕ) :
    IsZero ((LocallyFiniteExhaustion.Cycles.exhaustionRelativeStage (TopCat.of M) E i).homology (2 * p + 1)) :=
  ManifoldCompactSupport.Cycles.isZero_complexManifold_compactSupport p (E i) (E.isCompact i) (2 * p + 1)
    (Nat.lt_succ_self (2 * p))

variable [SecondCountableTopology M]

/-- Finite-dimensional complex charts give local compactness, and second
countability gives a genuine compact exhaustion. -/
def complexManifoldCompactExhaustion : CompactExhaustion M := by
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Fin p → ℂ) M
  exact CompactExhaustion.choice M

/-- Actual compact restrictions determine top-degree locally finite
homology, with next-degree vanishing discharged by the manifold theorem. -/
theorem complexLocallyFiniteHomology_compact_ext
    (a b : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ (TopCat.of M)).homology (2 * p))
    (hab : ∀ (K : Set M) (hK : IsCompact K),
      LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction (TopCat.of M) K hK (2 * p) a =
        LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction (TopCat.of M) K hK (2 * p) b) : a = b := by
  let E := complexManifoldCompactExhaustion p M
  exact LocallyFiniteExhaustion.Cycles.locallyFinite_homology_class_eq_of_exhaustion_restrictions (TopCat.of M) E (2 * p)
    (complexExhaustion_nextHomology_isZero p M E) a b (fun i => hab (E i) (E.isCompact i))

/-- Point restrictions determine top-degree locally finite homology of
the manifold. This does not assume a fundamental class. -/
theorem complexLocallyFiniteHomology_point_ext
    (a b : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ (TopCat.of M)).homology (2 * p))
    (hab : ∀ x : M, LocallyFiniteCompactRestriction.Cycles.locallyFinitePointHomologyRestriction (TopCat.of M) x (2 * p) a =
      LocallyFiniteCompactRestriction.Cycles.locallyFinitePointHomologyRestriction (TopCat.of M) x (2 * p) b) : a = b := by
  apply complexLocallyFiniteHomology_compact_ext p M a b
  intro K hK
  apply ManifoldCompactSupport.Cycles.complexManifold_compactSupport_point_ext p K hK
  intro x hx
  rw [locallyFiniteCompactHomologyRestriction_toPoint_apply,
    locallyFiniteCompactHomologyRestriction_toPoint_apply]
  exact hab x

variable [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M]

/-- The actual compact fundamental classes lift to a locally finite
homology class which restricts correctly on every compact subset. -/
theorem exists_complexLocallyFiniteFundamentalClass :
    ∃ a : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ (TopCat.of M)).homology (2 * p),
      ∀ (K : Set M) (hK : IsCompact K),
        LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction (TopCat.of M) K hK (2 * p) a =
          ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p K hK := by
  let E := complexManifoldCompactExhaustion p M
  obtain ⟨a, ha⟩ := LocallyFiniteExhaustion.Cycles.exists_locallyFinite_homology_class_of_coherent_exhaustion
    (TopCat.of M) E (2 * p)
    (fun i => ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (E i) (E.isCompact i))
    (fun i => ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_restriction p (E i) (E (i + 1))
      (E.isCompact i) (E.isCompact (i + 1)) (E.subset_succ i))
  refine ⟨a, fun K hK => ?_⟩
  obtain ⟨i, hi⟩ := E.exists_superset_of_isCompact hK
  calc
    LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction (TopCat.of M) K hK (2 * p) a =
        CompactSupportAssembly.Cycles.homologyWithSupportRestriction (TopCat.of M) hi (2 * p)
          (LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction (TopCat.of M) (E i) (E.isCompact i)
            (2 * p) a) :=
      (ConcreteCategory.congr_hom
        (locallyFiniteCompactHomologyRestriction_supportRestriction (TopCat.of M)
          hK (E.isCompact i) hi (2 * p)) a).symm
    _ = ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p K hK := by
      rw [ha i]
      exact ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_restriction p K (E i) hK (E.isCompact i) hi

/-- The canonical integral locally finite fundamental class of a
Hausdorff second-countable complex manifold of complex dimension p. -/
def complexLocallyFiniteFundamentalClass :
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ (TopCat.of M)).homology (2 * p) :=
  (exists_complexLocallyFiniteFundamentalClass p M).choose

/-- The canonical class restricts to the proved canonical class on every
compact support, not only on the chosen exhaustion. -/
theorem complexLocallyFiniteFundamentalClass_restriction (K : Set M) (hK : IsCompact K) :
    LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction (TopCat.of M) K hK (2 * p)
        (complexLocallyFiniteFundamentalClass p M) =
      ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p K hK :=
  (exists_complexLocallyFiniteFundamentalClass p M).choose_spec K hK

/-- The point value is the actual chart-independent complex local generator. -/
theorem complexLocallyFiniteFundamentalClass_atPoint (x : M) :
    LocallyFiniteCompactRestriction.Cycles.locallyFinitePointHomologyRestriction (TopCat.of M) x (2 * p)
        (complexLocallyFiniteFundamentalClass p M) =
      ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x := by
  rw [← locallyFiniteCompactHomologyRestriction_toPoint_apply (TopCat.of M)
    {x} isCompact_singleton x (mem_singleton x) (2 * p),
    complexLocallyFiniteFundamentalClass_restriction]
  exact ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_atPoint p {x} isCompact_singleton x (mem_singleton x)

/-- Canonical local values uniquely characterize the actual locally finite class. -/
theorem complexLocallyFiniteFundamentalClass_unique
    (a : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ (TopCat.of M)).homology (2 * p))
    (ha : ∀ x : M, LocallyFiniteCompactRestriction.Cycles.locallyFinitePointHomologyRestriction (TopCat.of M) x (2 * p) a =
      ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x) : a = complexLocallyFiniteFundamentalClass p M := by
  apply complexLocallyFiniteHomology_point_ext p M a
  intro x
  rw [ha x, complexLocallyFiniteFundamentalClass_atPoint]

/-- Existence and uniqueness are in the homology of the genuine spatially
locally finite singular complex. -/
theorem existsUnique_complexLocallyFiniteFundamentalClass :
    ∃! a : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ (TopCat.of M)).homology (2 * p),
      ∀ x : M, LocallyFiniteCompactRestriction.Cycles.locallyFinitePointHomologyRestriction (TopCat.of M) x (2 * p) a =
        ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x :=
  ⟨complexLocallyFiniteFundamentalClass p M,
    complexLocallyFiniteFundamentalClass_atPoint p M,
    complexLocallyFiniteFundamentalClass_unique p M⟩

/-- Every compact exhaustion produces the same class; the vanishing needed
for uniqueness is supplied by the manifold dimension theorem. -/
theorem complexLocallyFiniteFundamentalClass_unique_of_exhaustion
    (E : CompactExhaustion M)
    (a : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ (TopCat.of M)).homology (2 * p))
    (ha : ∀ i, LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction (TopCat.of M) (E i) (E.isCompact i)
      (2 * p) a = ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (E i) (E.isCompact i)) :
    a = complexLocallyFiniteFundamentalClass p M := by
  apply LocallyFiniteExhaustion.Cycles.locallyFinite_homology_class_eq_of_exhaustion_restrictions (TopCat.of M) E (2 * p)
    (complexExhaustion_nextHomology_isZero p M E) a
  intro i
  rw [ha i, complexLocallyFiniteFundamentalClass_restriction]

/-- The canonical locally finite class is nonzero on every nonempty manifold. -/
theorem complexLocallyFiniteFundamentalClass_ne_zero [Nonempty M] :
    complexLocallyFiniteFundamentalClass p M ≠ 0 := by
  intro hzero
  obtain ⟨x⟩ := ‹Nonempty M›
  have hx := complexLocallyFiniteFundamentalClass_atPoint p M x
  rw [hzero, map_zero] at hx
  exact ComplexChartOrientation.Cycles.complexCanonicalLocalClass_ne_zero x hx.symm

variable [CompactSpace M]

/-- On a compact complex manifold, the proved locally-finite/ordinary
comparison sends this class to the ordinary fundamental class. -/
theorem complexLocallyFiniteFundamentalClass_compactComparison :
    (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryHomologyIso ℤ (TopCat.of M) (2 * p)).hom
        (complexLocallyFiniteFundamentalClass p M) =
      CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass p M := by
  apply CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass_unique p M
  intro x
  have h := ConcreteCategory.congr_hom
    (LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction_eq_compactComparison (TopCat.of M)
      {x} isCompact_singleton (2 * p)) (complexLocallyFiniteFundamentalClass p M)
  exact h.symm.trans (complexLocallyFiniteFundamentalClass_atPoint p M x)

/-- Equivalently, ordinary inclusion into locally finite chains sends the
ordinary compact fundamental class to the canonical locally finite class. -/
theorem complexManifoldFundamentalClass_toLocallyFinite :
    (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteHomologyIso ℤ (TopCat.of M) (2 * p)).hom
        (CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass p M) =
      complexLocallyFiniteFundamentalClass p M := by
  let e := LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteHomologyIso ℤ (TopCat.of M) (2 * p)
  apply e.toLinearEquiv.symm.injective
  change e.inv (e.hom (CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass p M)) =
    e.inv (complexLocallyFiniteFundamentalClass p M)
  exact (ConcreteCategory.congr_hom e.hom_inv_id (CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass p M)).trans
    (complexLocallyFiniteFundamentalClass_compactComparison p M).symm

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles
