import OAI.AlgebraicGeometry.CycleClass.Geometric.EventuallySmall
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivisionHomotopy

/-! # Iterated Subdivision Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.IteratedSubdivisionHomotopy

noncomputable section

/-!
# Iterated subdivision homotopies with support control

The actual natural subdivision homotopy is composed finitely many times.
Evaluation gives a homotopy from every actual subdivision iterate to the
identity. Its negative gives the prism operator with convention
`id - Sd^N = d K_N + K_N d`, retaining naturality and spatial support control.
-/

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

/-- Evaluation of natural singular-chain endomorphisms preserves composition. -/
@[simp]
theorem naturalSingularChainMapAt_comp
    (f g : SubdivisionHomotopy.Cycles.naturalSingularChains ⟶ SubdivisionHomotopy.Cycles.naturalSingularChains) (X : TopCat.{0}) :
    SubdivisionHomotopy.Cycles.naturalSingularChainMapAt (f ≫ g) X =
      SubdivisionHomotopy.Cycles.naturalSingularChainMapAt f X ≫ SubdivisionHomotopy.Cycles.naturalSingularChainMapAt g X := rfl

/-- The actual subdivision iterates, simultaneously on all spaces. -/
def naturalSubdivisionIterate : ℕ → (SubdivisionHomotopy.Cycles.naturalSingularChains ⟶ SubdivisionHomotopy.Cycles.naturalSingularChains) :=
  Nat.rec (𝟙 _) (fun _ s => s ≫ SubdivisionHomotopy.Cycles.naturalSubdivision)

/-- Evaluating the natural iterate recovers exactly the actual chain-map iterate. -/
theorem naturalSubdivisionIterate_at (X : TopCat.{0}) (N : ℕ) :
    SubdivisionHomotopy.Cycles.naturalSingularChainMapAt (naturalSubdivisionIterate N) X =
      EventuallySmall.Cycles.iterateChainMap (SubdivisionBoundary.Cycles.subdivisionChainMap X) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change SubdivisionHomotopy.Cycles.naturalSingularChainMapAt (naturalSubdivisionIterate N ≫ SubdivisionHomotopy.Cycles.naturalSubdivision) X =
      EventuallySmall.Cycles.iterateChainMap (SubdivisionBoundary.Cycles.subdivisionChainMap X) N ≫ SubdivisionBoundary.Cycles.subdivisionChainMap X
    rw [naturalSingularChainMapAt_comp, ih]
    rfl

/-- Finite composition of the already constructed natural subdivision homotopy. -/
def naturalSubdivisionIterateHomotopy (N : ℕ) :
    Homotopy (naturalSubdivisionIterate N) (𝟙 SubdivisionHomotopy.Cycles.naturalSingularChains) := by
  induction N with
  | zero => exact Homotopy.refl _
  | succ N ih =>
    exact (SubdivisionHomotopy.Cycles.naturalSubdivisionHomotopy.compLeftId (naturalSubdivisionIterate N)).trans ih

/-- Each actual subdivision iterate is homotopic to the identity. -/
def iteratedSubdivisionHomotopy (X : TopCat.{0}) (N : ℕ) :
    Homotopy (EventuallySmall.Cycles.iterateChainMap (SubdivisionBoundary.Cycles.subdivisionChainMap X) N) (𝟙 (LocalHomology.Cycles.integralSingularChains X)) :=
  (Homotopy.ofEq (naturalSubdivisionIterate_at X N).symm).trans
    (SubdivisionHomotopy.Cycles.naturalSingularHomotopyAt (naturalSubdivisionIterateHomotopy N) X)

/-- The components are evaluations of the explicit finite natural homotopy. -/
@[simp]
theorem iteratedSubdivisionHomotopy_hom (X : TopCat.{0}) (N i j : ℕ) :
    (iteratedSubdivisionHomotopy X N).hom i j =
      ((naturalSubdivisionIterateHomotopy N).hom i j).app X := by
  simp [iteratedSubdivisionHomotopy, Homotopy.trans, Homotopy.ofEq,
    SubdivisionHomotopy.Cycles.naturalSingularHomotopyAt]

/-- The sign convention useful for smallification is `id - Sd^N = dK + Kd`. -/
def iteratedSubdivisionContraction (X : TopCat.{0}) (N : ℕ) :
    Homotopy (𝟙 (LocalHomology.Cycles.integralSingularChains X)) (EventuallySmall.Cycles.iterateChainMap (SubdivisionBoundary.Cycles.subdivisionChainMap X) N) :=
  (iteratedSubdivisionHomotopy X N).symm

/-- The reverse homotopy is still an actual natural operation in each degree. -/
@[simp]
theorem iteratedSubdivisionContraction_hom (X : TopCat.{0}) (N i j : ℕ) :
    (iteratedSubdivisionContraction X N).hom i j =
      (-((naturalSubdivisionIterateHomotopy N).hom i j)).app X := by
  simp [iteratedSubdivisionContraction, Homotopy.symm,
    iteratedSubdivisionHomotopy_hom]

/-- Naturality of every iterated homotopy component under continuous maps. -/
theorem iteratedSubdivisionHomotopy_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (N i j : ℕ) :
    (LocalHomology.Cycles.integralSingularChainFunctor.map f).f i ≫ (iteratedSubdivisionHomotopy Y N).hom i j =
      (iteratedSubdivisionHomotopy X N).hom i j ≫
        (LocalHomology.Cycles.integralSingularChainFunctor.map f).f j := by
  simp only [iteratedSubdivisionHomotopy_hom]
  exact ((naturalSubdivisionIterateHomotopy N).hom i j).naturality f

/-- Naturality also holds with the smallification sign convention. -/
theorem iteratedSubdivisionContraction_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (N i j : ℕ) :
    (LocalHomology.Cycles.integralSingularChainFunctor.map f).f i ≫
        (iteratedSubdivisionContraction Y N).hom i j =
      (iteratedSubdivisionContraction X N).hom i j ≫
        (LocalHomology.Cycles.integralSingularChainFunctor.map f).f j := by
  simp only [iteratedSubdivisionContraction_hom]
  exact (-((naturalSubdivisionIterateHomotopy N).hom i j)).naturality f

/-- Each iterated homotopy component commutes with actual subspace inclusion. -/
theorem iteratedSubdivisionHomotopy_subspace (X : TopCat.{0}) (A : Set X) (N i j : ℕ) :
    (LocalHomology.Cycles.subspaceChainInclusion X A).f i ≫ (iteratedSubdivisionHomotopy X N).hom i j =
      (iteratedSubdivisionHomotopy (TopCat.of A) N).hom i j ≫
        (LocalHomology.Cycles.subspaceChainInclusion X A).f j :=
  iteratedSubdivisionHomotopy_naturality (LocalHomology.Cycles.subspaceInclusion X A) N i j

/-- Each prism homotopy component commutes with actual subspace inclusion. -/
theorem iteratedSubdivisionContraction_subspace
    (X : TopCat.{0}) (A : Set X) (N i j : ℕ) :
    (LocalHomology.Cycles.subspaceChainInclusion X A).f i ≫ (iteratedSubdivisionContraction X N).hom i j =
      (iteratedSubdivisionContraction (TopCat.of A) N).hom i j ≫
        (LocalHomology.Cycles.subspaceChainInclusion X A).f j :=
  iteratedSubdivisionContraction_naturality (LocalHomology.Cycles.subspaceInclusion X A) N i j

/-- Every component of the iterated homotopy preserves the actual image of
the chain complex of each subspace. -/
theorem iteratedSubdivisionHomotopy_preserves_subspaceImage
    (X : TopCat.{0}) (A : Set X) (N i j : ℕ)
    {c : (LocalHomology.Cycles.integralSingularChains X).X i}
    (hc : c ∈ LinearMap.range ((LocalHomology.Cycles.subspaceChainInclusion X A).f i).hom) :
    (iteratedSubdivisionHomotopy X N).hom i j c ∈
      LinearMap.range ((LocalHomology.Cycles.subspaceChainInclusion X A).f j).hom := by
  obtain ⟨b, rfl⟩ := hc
  refine ⟨(iteratedSubdivisionHomotopy (TopCat.of A) N).hom i j b, ?_⟩
  exact (ConcreteCategory.congr_hom
    (iteratedSubdivisionHomotopy_subspace X A N i j) b).symm

/-- Every component of the reversed homotopy has the same subspace-image
preservation, with no openness hypothesis. -/
theorem iteratedSubdivisionContraction_preserves_subspaceImage
    (X : TopCat.{0}) (A : Set X) (N i j : ℕ)
    {c : (LocalHomology.Cycles.integralSingularChains X).X i}
    (hc : c ∈ LinearMap.range ((LocalHomology.Cycles.subspaceChainInclusion X A).f i).hom) :
    (iteratedSubdivisionContraction X N).hom i j c ∈
      LinearMap.range ((LocalHomology.Cycles.subspaceChainInclusion X A).f j).hom := by
  obtain ⟨b, rfl⟩ := hc
  refine ⟨(iteratedSubdivisionContraction (TopCat.of A) N).hom i j b, ?_⟩
  exact (ConcreteCategory.congr_hom
    (iteratedSubdivisionContraction_subspace X A N i j) b).symm

/-- The iterated homotopy preserves the actual image of the small-chain
complex for every family of subsets, without openness assumptions. -/
theorem iteratedSubdivisionHomotopy_preserves_smallChainImage
    (X : TopCat.{0}) {J : Type} (U : J → Set X) (N i j : ℕ)
    {c : (LocalHomology.Cycles.integralSingularChains X).X i}
    (hc : c ∈ LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f i).hom) :
    (iteratedSubdivisionHomotopy X N).hom i j c ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f j).hom := by
  rw [iteratedSubdivisionHomotopy_hom]
  exact AlgebraicTopology.Cohomology.Singular.NaturalSmallChains.naturalSingularOperation_preserves_smallChainImage
    ((naturalSubdivisionIterateHomotopy N).hom i j) X U hc

/-- The same small-chain preservation for the reversed homotopy. -/
theorem iteratedSubdivisionContraction_preserves_smallChainImage
    (X : TopCat.{0}) {J : Type} (U : J → Set X) (N i j : ℕ)
    {c : (LocalHomology.Cycles.integralSingularChains X).X i}
    (hc : c ∈ LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f i).hom) :
    (iteratedSubdivisionContraction X N).hom i j c ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f j).hom := by
  rw [iteratedSubdivisionContraction_hom]
  exact AlgebraicTopology.Cohomology.Singular.NaturalSmallChains.naturalSingularOperation_preserves_smallChainImage
    (-((naturalSubdivisionIterateHomotopy N).hom i j)) X U hc

/-- The actual degree-raising integral prism operator `K_N`. -/
def subdivisionPrism (X : TopCat.{0}) (N n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (LocalHomology.Cycles.integralSingularChains X).X (n + 1) :=
  ((iteratedSubdivisionContraction X N).hom n (n + 1)).hom

/-- The prism of a chain from a subspace is still a chain from that subspace. -/
theorem subdivisionPrism_preserves_subspaceImage
    (X : TopCat.{0}) (A : Set X) (N n : ℕ)
    {c : (LocalHomology.Cycles.integralSingularChains X).X n}
    (hc : c ∈ LinearMap.range ((LocalHomology.Cycles.subspaceChainInclusion X A).f n).hom) :
    subdivisionPrism X N n c ∈
      LinearMap.range ((LocalHomology.Cycles.subspaceChainInclusion X A).f (n + 1)).hom := by
  obtain ⟨b, rfl⟩ := hc
  refine ⟨subdivisionPrism (TopCat.of A) N n b, ?_⟩
  exact (ConcreteCategory.congr_hom
    (iteratedSubdivisionContraction_subspace X A N n (n + 1)) b).symm

/-- The prism of a cover-small chain is again cover-small. -/
theorem subdivisionPrism_preserves_smallChainImage
    (X : TopCat.{0}) {J : Type} (U : J → Set X) (N n : ℕ)
    {c : (LocalHomology.Cycles.integralSingularChains X).X n}
    (hc : c ∈ LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom) :
    subdivisionPrism X N n c ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f (n + 1)).hom :=
  iteratedSubdivisionContraction_preserves_smallChainImage X U N n (n + 1) hc

/-- Support-level form of the prism's cover-small preservation. -/
theorem subdivisionPrism_preserves_small_support
    (X : TopCat.{0}) {J : Type} (U : J → Set X) (N n : ℕ)
    {c : (LocalHomology.Cycles.integralSingularChains X).X n}
    (hc : ∀ s ∈ SingularChainSupport.Cycles.singularChainSupport c,
      s ∈ (AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U).obj (.op ⦋n⦌)) :
    ∀ t ∈ SingularChainSupport.Cycles.singularChainSupport (subdivisionPrism X N n c),
      t ∈ (AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U).obj (.op ⦋n + 1⦌) :=
  (SmallChainImage.Cycles.mem_range_smallIntegralChainInclusion_iff X U (n + 1) _).mp
    (subdivisionPrism_preserves_smallChainImage X U N n
      ((SmallChainImage.Cycles.mem_range_smallIntegralChainInclusion_iff X U n c).mpr hc))

/-- The exact prism identity in every positive chain degree. -/
theorem subdivisionPrism_boundary (X : TopCat.{0}) (N n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1)) :
    c - (EventuallySmall.Cycles.iterateChainMap (SubdivisionBoundary.Cycles.subdivisionChainMap X) N).f (n + 1) c =
      (LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1) (subdivisionPrism X N (n + 1) c) +
        subdivisionPrism X N n ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c) := by
  have hm := (iteratedSubdivisionContraction X N).comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hm
  have h := congrArg (fun f : (LocalHomology.Cycles.integralSingularChains X).X (n + 1) ⟶
      (LocalHomology.Cycles.integralSingularChains X).X (n + 1) => f.hom c) hm
  change c =
    subdivisionPrism X N n ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c) +
      (LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1) (subdivisionPrism X N (n + 1) c) +
        (EventuallySmall.Cycles.iterateChainMap (SubdivisionBoundary.Cycles.subdivisionChainMap X) N).f (n + 1) c at h
  apply sub_eq_iff_eq_add.mpr
  exact h.trans (by ac_rfl)

/-- The degree-zero prism identity has no incoming-boundary term. -/
theorem subdivisionPrism_boundary_zero (X : TopCat.{0}) (N : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X 0) :
    c - (EventuallySmall.Cycles.iterateChainMap (SubdivisionBoundary.Cycles.subdivisionChainMap X) N).f 0 c =
      (LocalHomology.Cycles.integralSingularChains X).d 1 0 (subdivisionPrism X N 0 c) := by
  have hm := (iteratedSubdivisionContraction X N).comm 0
  rw [Homotopy.dNext_zero_chainComplex, zero_add, Homotopy.prevD_chainComplex] at hm
  have h := congrArg (fun f : (LocalHomology.Cycles.integralSingularChains X).X 0 ⟶
      (LocalHomology.Cycles.integralSingularChains X).X 0 => f.hom c) hm
  change c = (LocalHomology.Cycles.integralSingularChains X).d 1 0 (subdivisionPrism X N 0 c) +
    (EventuallySmall.Cycles.iterateChainMap (SubdivisionBoundary.Cycles.subdivisionChainMap X) N).f 0 c at h
  exact sub_eq_iff_eq_add.mpr h

/-- The exact correction identity used to replace a chain by a small chain
while keeping its boundary fixed. -/
theorem subdivisionPrism_boundary_correction (X : TopCat.{0}) (N n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1)) :
    c - ((EventuallySmall.Cycles.iterateChainMap (SubdivisionBoundary.Cycles.subdivisionChainMap X) N).f (n + 1) c +
        subdivisionPrism X N n ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c)) =
      (LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1) (subdivisionPrism X N (n + 1) c) := by
  apply sub_eq_iff_eq_add.mpr
  exact (sub_eq_iff_eq_add.mp (subdivisionPrism_boundary X N n c)).trans (by ac_rfl)

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.IteratedSubdivisionHomotopy
