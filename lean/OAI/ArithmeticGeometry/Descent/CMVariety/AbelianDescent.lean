import OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicPoints
import OAI.ArithmeticGeometry.Descent.CMVariety.Rigidity
import OAI.ArithmeticGeometry.Descent.CMVariety.SplitPeriods
import OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli
import OAI.ArithmeticGeometry.Descent.CMVariety.FiniteGeometricPoints
import OAI.ArithmeticGeometry.Descent.CMVariety.GraphCM
import OAI.AlgebraicGeometry.ComplexMultiplication.CMCore

/-! # Abelian Descent -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AbelianDescent

noncomputable section

/-!
CMAbelianVariety proof infrastructure. Both unconditional conclusions are proved in
CMAbelianDescent and ModuliCMDescent. Those modules import the
CM-enhancement bridge separately to keep the dependency graph acyclic.

The abelian-variety proof constructs an embedded smooth proper
geometrically connected commutative group family over finite rational
coefficient rings, with the original complex group as its exact fiber.
The dominant complex fiber fixes its relative dimension. A smooth
arithmetic parameter retains the finite algebraic endomorphism tuple
constructed from the original Hodge-theoretic CM hypothesis.

The analytic proof constructs actual fiber exponentials, logarithms,
full integral period bases, and the endomorphism-period comparison.
The fixed CM tuple then gives nearby algebraic group isomorphisms.
Etale coordinates prove density of actual number-field points in the
smooth arithmetic parameter. Specializing at one such point supplies
the exact smooth proper geometrically connected number-field group
model and its group-preserving complex-fiber isomorphism.

For the moduli-point theorem, the constructed smooth enhanced parameter
retains polarization, duality, Poincare data, full level, and designated
endomorphisms. Local group rigidity and countability of actual maps to
the dual give a countable local image in the represented moduli space.
An open arithmetic chart and the isolated-point descent bridge yield
the exact number-field factorization of the original moduli point.

The declarations below record foundational period-rigidity and arithmetic
descent steps used by these proofs.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The committed Hodge-theoretic CM hypothesis supplies a splitting with
only finitely many compatible enhanced periods. This is a statement about
the actual rational H¹ of the abelian variety, without a moduli assumption. -/
theorem hasCMH1_finitely_many_enhanced_periods
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (hCM : A.HasCMH1) :
    ∃ (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
      (D : AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition H),
      H.holomorphic = A.h1Holomorphic ∧
      H.antiholomorphic = A.h1Antiholomorphic ∧
      Finite (SplitPeriods.Abelian.SplitCMPeriod D) := by
  obtain ⟨H, hhol, hanti, ⟨D⟩⟩ := hCM
  exact ⟨H, D, hhol, hanti, SplitPeriods.Abelian.split_CM_periods_finite D⟩

/-- The original CM hypothesis supplies a finite tuple of rational
endomorphisms preserving the actual Hodge types. The actual holomorphic
space is the unique invariant complement of the antiholomorphic space.
This proves linear period rigidity without assuming a period chart. -/
theorem hasCMH1_finite_rational_enhancement_rigid
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (hCM : A.HasCMH1) :
    ∃ (r : ℕ) (f : Fin r →
        (A.variety.rationalCohomology 1 →ₗ[ℚ] A.variety.rationalCohomology 1)),
      (∀ i x, x ∈ A.h1Holomorphic → (f i).baseChange ℂ x ∈ A.h1Holomorphic) ∧
      (∀ i x, x ∈ A.h1Antiholomorphic → (f i).baseChange ℂ x ∈ A.h1Antiholomorphic) ∧
      ∀ W : Submodule ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1)),
        IsCompl W A.h1Antiholomorphic →
        (∀ i x, x ∈ W → (f i).baseChange ℂ x ∈ W) →
        W = A.h1Holomorphic := by
  classical
  obtain ⟨H, hhol, hanti, ⟨D⟩⟩ := hCM
  let e := Fintype.equivFin (GraphCM.Abelian.CMGraph.ParameterIndex D)
  refine ⟨Fintype.card (GraphCM.Abelian.CMGraph.ParameterIndex D),
    fun i => GraphCM.Abelian.CMGraph.separatingOperator D (e.symm i), ?_, ?_, ?_⟩
  · intro i x hx
    rw [← hhol] at hx ⊢
    exact GraphCM.Abelian.CMGraph.separatingOperator_hodge D (e.symm i) x hx
  · intro i x hx
    rw [← hanti] at hx ⊢
    exact (GraphCM.Abelian.CMGraph.separatingOperator_hodge D (e.symm i)).map_antiholomorphic hx
  · intro W hW hInv
    rw [← hanti] at hW
    rw [← hhol]
    apply GraphCM.Abelian.CMGraph.invariant_complement_eq_holomorphic D W hW
    intro t x hx
    simpa only [e.symm_apply_apply] using hInv (e t) x hx

/-- The descent step in the enhanced-moduli argument, for actual schemes:
an isolated enhanced complex point gives an algebraic point after applying
any algebraic forgetful morphism. This does not assert that CM supplies
the enhanced scheme or the isolated point. -/
theorem isolated_enhanced_point_descends
    {X Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of ℚ))
    [LocallyOfFiniteType f] (forget : Y ⟶ X)
    (p : Spec (CommRingCat.of ℂ) ⟶
      CategoryTheory.Limits.pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
    (hp : IsOpen {p (IsLocalRing.closedPoint ℂ)}) :
    ∃ (K : Subfield ℂ), NumberField K ∧
      ∃ pK : Spec (CommRingCat.of K) ⟶ X,
        Spec.map (CommRingCat.ofHom K.subtype) ≫ pK =
          p ≫ CategoryTheory.Limits.pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) ≫ forget := by
  obtain ⟨K, hK, q, hq⟩ := AlgebraicPoints.Abelian.complex_point_descends_of_isolated_baseChange f p hp
  refine ⟨K, hK, q ≫ forget, ?_⟩
  rw [← Category.assoc, hq, Category.assoc]

/-- Once the enhanced arithmetic parameter point is isolated, both exact
CMAbelianVariety conclusions follow: the moduli point is algebraic and its actual
abelian variety has a group-preserving number-field model. -/
theorem isolated_enhancement_gives_point_and_abelian_descent
    (M : StandardModuli.Abelian.StandardAbelianModuli)
    {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of ℚ))
    [LocallyOfFiniteType f] (forget : Y ⟶ M.space)
    (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ CategoryTheory.Limits.pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
    (hp : IsOpen {p (IsLocalRing.closedPoint ℂ)}) :
    let x := p ≫ CategoryTheory.Limits.pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) ≫ forget
    M.IsAlgebraicPoint x ∧ AbelianFiber.HasNumberFieldModel (M.abelianAt x) := by
  dsimp only
  have hx := isolated_enhanced_point_descends f forget p hp
  exact ⟨hx, M.abelianAt_descends_of_point_descends _ hx⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AbelianDescent
