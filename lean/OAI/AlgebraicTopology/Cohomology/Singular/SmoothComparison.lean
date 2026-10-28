import OAI.AlgebraicTopology.Cohomology.Singular.SmoothHomotopy
import OAI.AlgebraicTopology.Cohomology.Singular.Homotopy
import OAI.AlgebraicTopology.Cohomology.Singular.Contractible

/-! # Smooth Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SmoothComparison

noncomputable section

/-!
# Smooth-versus-continuous singular comparison on a normed space

For a real normed vector space, the actual inclusion of smooth singular
simplices into continuous singular simplices is a chain homotopy equivalence.
Its inverse up to homotopy is the constant simplicial map at a chosen point.
The two composites are contracted using genuine simplicial homotopies.

This proves a local comparison theorem on normed model spaces; it does not
assert a global smoothing theorem on arbitrary manifolds.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The constant smooth zero-simplex at a selected point. -/
def smoothPointSimplex (c : E) : (Smooth.smoothSingularSubcomplex E).toSSet _⦋0⦌ :=
  ⟨((TopCat.of E).toSSetObjEquiv _).symm (ContinuousMap.const _ c), by
    change Smooth.IsSmoothSimplex _
    simp only [Equiv.apply_symm_apply]
    exact Smooth.isSmoothSimplex_const 0 c⟩

/-- A simplicial inverse to the smooth inclusion, up to homotopy. It sends
all simplices to the constant smooth simplex at `c`. -/
def smoothComparisonRetraction (c : E) :
    TopCat.toSSet.obj (TopCat.of E) ⟶ (Smooth.smoothSingularSubcomplex E).toSSet :=
  SSet.const (smoothPointSimplex c)

theorem smoothInclusion_retraction (c : E) :
    Smooth.smoothSingularInclusion E ≫ smoothComparisonRetraction c =
      SmoothFunctor.smoothSingularMap (fun _ : E => c) contDiff_const := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.ext_apply
  intro σ
  apply Subtype.ext
  apply ((TopCat.of E).toSSetObjEquiv n).injective
  ext x
  rfl

theorem smoothRetraction_inclusion (c : E) :
    smoothComparisonRetraction c ≫ Smooth.smoothSingularInclusion E =
      TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const E c)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.ext_apply
  intro σ
  apply ((TopCat.of E).toSSetObjEquiv n).injective
  ext x
  rfl

/-- The ordinary continuous linear contraction of a normed vector space. -/
def continuousLinearContraction (c : E) :
    TopCat.Homotopy (𝟙 (TopCat.of E))
      (TopCat.ofHom (ContinuousMap.const E c)) where
  toFun p := (1 - (p.1 : ℝ)) • p.2 + (p.1 : ℝ) • c
  continuous_toFun := by fun_prop
  map_zero_left x := by simp
  map_one_left x := by simp

/-- The smooth composite is simplicially homotopic to the identity. -/
def smoothComparisonHomotopy (c : E) :
    SSet.Homotopy (𝟙 (Smooth.smoothSingularSubcomplex E).toSSet)
      (Smooth.smoothSingularInclusion E ≫ smoothComparisonRetraction c) := by
  rw [smoothInclusion_retraction]
  exact SmoothHomotopy.smoothLinearContraction c

/-- The continuous composite is simplicially homotopic to the identity. -/
def continuousComparisonHomotopy (c : E) :
    SSet.Homotopy (𝟙 (TopCat.toSSet.obj (TopCat.of E)))
      (smoothComparisonRetraction c ≫ Smooth.smoothSingularInclusion E) := by
  rw [smoothRetraction_inclusion]
  have h := (continuousLinearContraction c).toSSet
  rw [TopCat.toSSet.map_id] at h
  exact h

variable {R : Type} [Ring R]

/-- The genuine smooth-to-continuous chain inclusion is a chain homotopy
equivalence on every real normed vector space. -/
def smoothChainComparisonHomotopyEquiv (M : ModuleCat.{0} R) (c : E) :
    _root_.HomotopyEquiv (Smooth.smoothSingularChains M E)
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex M) where
  hom := Smooth.smoothSingularChainInclusion M E
  inv := SSet.chainComplexMap (smoothComparisonRetraction c) M
  homotopyHomInvId := by
    have H := ((smoothComparisonHomotopy c).chainComplexMap M).symm
    dsimp only [SSet.chainComplexMap] at H
    rw [((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj M).map_id,
      ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj M).map_comp] at H
    exact H
  homotopyInvHomId := by
    have H := ((continuousComparisonHomotopy c).chainComplexMap M).symm
    dsimp only [SSet.chainComplexMap] at H
    rw [((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj M).map_id,
      ((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj M).map_comp] at H
    exact H

/-- The existing restriction is the simplicial pullback along the actual inclusion. -/
theorem smoothRestriction_eq_simplicialPullback (M : ModuleCat.{0} R) :
    Smooth.smoothSingularCochainRestriction M E =
      Functor.simplicialPullback M (Smooth.smoothSingularInclusion E) := rfl

/-- Restriction to the smooth singular simplices is a cochain homotopy
equivalence on every real normed vector space. -/
def smoothCochainComparisonHomotopyEquiv (M : ModuleCat.{0} R) (c : E) :
    _root_.HomotopyEquiv (Basic.singularCochains M (TopCat.of E))
      (Smooth.smoothSingularCochains M E) where
  hom := Smooth.smoothSingularCochainRestriction M E
  inv := Functor.simplicialPullback M (smoothComparisonRetraction c)
  homotopyHomInvId := by
    simpa only [Functor.simplicialPullback_comp, Functor.simplicialPullback_id,
      smoothRestriction_eq_simplicialPullback] using
      (Singular.Homotopy.simplicialPullbackHomotopy M (continuousComparisonHomotopy c)).symm
  homotopyInvHomId := by
    simpa only [Functor.simplicialPullback_comp, Functor.simplicialPullback_id,
      smoothRestriction_eq_simplicialPullback] using
      (Singular.Homotopy.simplicialPullbackHomotopy M (smoothComparisonHomotopy c)).symm

/-- Actual cohomology comparison induced by restriction to smooth simplices. -/
def smoothCohomologyComparisonIso (M : ModuleCat.{0} R) (c : E) (n : ℕ) :
    Basic.singularCohomology M (TopCat.of E) n ≅ (Smooth.smoothSingularCochains M E).homology n :=
  (smoothCochainComparisonHomotopyEquiv M c).toHomologyIso n

/-- The forward comparison map is precisely the map on cohomology induced by
the already defined smooth-simplex restriction, not an arbitrarily chosen iso. -/
@[simp]
theorem smoothCohomologyComparisonIso_hom (M : ModuleCat.{0} R) (c : E) (n : ℕ) :
    (smoothCohomologyComparisonIso M c n).hom =
      HomologicalComplex.homologyMap (Smooth.smoothSingularCochainRestriction M E) n := rfl

/-- The actual restriction map induces isomorphisms in every cohomological degree. -/
theorem isIso_smoothCohomologyRestriction (M : ModuleCat.{0} R) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Smooth.smoothSingularCochainRestriction M E) n) := by
  change IsIso (smoothCohomologyComparisonIso M (0 : E) n).hom
  infer_instance

/-- Positive-degree smooth singular cohomology vanishes on real normed spaces. -/
theorem isZero_smoothSingularCohomology (M : ModuleCat.{0} R) (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero ((Smooth.smoothSingularCochains M E).homology n) :=
  (Contractible.isZero_singularCohomology_of_contractible M (TopCat.of E) n hn).of_iso
    (smoothCohomologyComparisonIso M (0 : E) n).symm

end

end OAI.AlgebraicTopology.Cohomology.Singular.SmoothComparison
