import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LatticePeriod

/-! # Intrinsic Weight -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps

/-! Transport genuine holomorphic torus homomorphisms to the native abelian varieties. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.IsIntegral A.toOver.left :=
  A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.Smooth A.toOver.hom :=
  A.variety.presentation.smooth

/-- The constructed uniformization also preserves the actual group operations. -/
def periodAddEquiv (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A).Point ≃+ Additive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) where
  toEquiv := (AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph hHolomorphicAlgebraicity A).toEquiv
  map_add' x y := by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact ExponentialM.Constructions.Exponential.expMap_add (E := Transport.Constructions.AbelianModel A) (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) v w

/-- A torus group map gives an actual native point-group homomorphism. -/
def nativeMap (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (g : (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity B).Point →+ (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A).Point) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver →* ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver :=
  let f := (periodAddEquiv hHolomorphicAlgebraicity A).toAddMonoidHom.comp
    (g.comp (periodAddEquiv hHolomorphicAlgebraicity B).symm.toAddMonoidHom)
  { toFun := f
    map_one' := f.map_zero
    map_mul' := f.map_add }

/-- Its point function is exactly conjugation by the proved native uniformizations. -/
theorem nativeMap_apply (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (g : (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity B).Point →+ (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A).Point)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver) :
    nativeMap hHolomorphicAlgebraicity A B g x = AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph hHolomorphicAlgebraicity A (g ((AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph hHolomorphicAlgebraicity B).symm x)) := rfl

/-- BettiLattice's genuine local holomorphic lifts give native complex differentiability. -/
theorem nativeMap_mdifferentiable (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (g : (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity B).Point →+ (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A).Point) (hg : Geometry.ComplexTorus.BettiLattice.CM.Construction.Holomorphic g) :
    MDifferentiable (𝓘(ℂ, Transport.Constructions.AbelianModel B)) (𝓘(ℂ, Transport.Constructions.AbelianModel A))
      (nativeMap hHolomorphicAlgebraicity A B g) := by
  have hgd := Torus.Constructions.LatticeQuotient.mdifferentiable_of_local_lifts
    (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) g hg
  exact (AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph_mdifferentiable hHolomorphicAlgebraicity A).comp
    (hgd.comp (AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph_symm_mdifferentiable hHolomorphicAlgebraicity B))

/-- The transported map has the exact commuting square on actual points. -/
theorem nativeMap_periodHomeomorph (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (g : (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity B).Point →+ (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A).Point)
    (x : (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity B).Point) :
    nativeMap hHolomorphicAlgebraicity A B g (AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph hHolomorphicAlgebraicity B x) = AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph hHolomorphicAlgebraicity A (g x) := by
  rw [nativeMap_apply]
  erw [Homeomorph.symm_apply_apply]

end AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps

namespace AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicPeriodNaturality

/-! The transported native group map induces the prescribed actual rational H¹ pullback. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions
  IntrinsicTorusMaps LatticePeriod.Constructions.LatticeDual

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.Smooth A.toOver.hom := A.variety.presentation.smooth

/-- The actual continuous uniformization, used for the singular pullback. -/
def uniformizationMap (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    SingularPeriodsD.Constructions.SingularPeriods.Base (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ⟶ TopCat.of A.variety.analyticSpace :=
  TopCat.ofHom ⟨AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph hHolomorphicAlgebraicity A, (AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph hHolomorphicAlgebraicity A).continuous⟩

/-- The rational lattice-dual comparison evaluates to the actual singular period. -/
theorem rationalH1Equiv_lattice (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (c : A.variety.rationalCohomology 1) (ℓ : AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A c (LatticePeriod.Constructions.LatticeDual.latticeInclusion (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ) =
      SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (uniformizationMap hHolomorphicAlgebraicity A) 1 c) ℓ := by
  have he := (LatticePeriod.Constructions.LatticeDual.characterRestrictionEquiv (K := ℚ) (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).apply_symm_apply
    (SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (uniformizationMap hHolomorphicAlgebraicity A) 1 c))
  exact DFunLike.congr_fun he ℓ

/-- Naturality uses the actual covering square and the proved singular period
comparison, so the cohomology action is the prescribed rational transpose. -/
theorem rationalH1Equiv_nativeMap_pullback (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (g : (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity B).Point →+ (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A).Point)
    (hg : Geometry.ComplexTorus.BettiLattice.CM.Construction.Holomorphic g)
    (f : (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity B).V →ₗ[ℂ] (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A).V)
    (fQ : (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity B).LQ →ₗ[ℚ] (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A).LQ)
    (hf : Geometry.ComplexTorus.BettiLattice.CM.Construction.PreservesLattice f) (hlift : Geometry.ComplexTorus.BettiLattice.CM.Construction.Lifts g f)
    (hfQ : ∀ v : (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity B).LQ, (fQ v : (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A).V) = f v)
    (c : A.variety.rationalCohomology 1) :
    AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity B
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom ⟨IntrinsicTorusMaps.nativeMap hHolomorphicAlgebraicity A B g,
          (IntrinsicTorusMaps.nativeMap_mdifferentiable hHolomorphicAlgebraicity A B g hg).continuous⟩) 1 c) =
      (AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A c).comp fQ := by
  let qA := uniformizationMap hHolomorphicAlgebraicity A
  let qB := uniformizationMap hHolomorphicAlgebraicity B
  let gn : TopCat.of B.variety.analyticSpace ⟶ TopCat.of A.variety.analyticSpace :=
    TopCat.ofHom ⟨IntrinsicTorusMaps.nativeMap hHolomorphicAlgebraicity A B g, (IntrinsicTorusMaps.nativeMap_mdifferentiable hHolomorphicAlgebraicity A B g hg).continuous⟩
  let gt : SingularPeriodsD.Constructions.SingularPeriods.Base (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) ⟶ SingularPeriodsD.Constructions.SingularPeriods.Base (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :=
    TopCat.ofHom ⟨g, (Torus.Constructions.LatticeQuotient.mdifferentiable_of_local_lifts
      (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) g hg).continuous⟩
  let ft : SingularPeriodsD.Constructions.SingularPeriods.Cover (V := Transport.Constructions.AbelianModel B) ⟶ SingularPeriodsD.Constructions.SingularPeriods.Cover (V := Transport.Constructions.AbelianModel A) :=
    TopCat.ofHom ⟨f, f.continuous_of_finiteDimensional⟩
  have hnative : qB ≫ gn = gt ≫ qA := by
    apply TopCat.ext
    intro x
    exact IntrinsicTorusMaps.nativeMap_periodHomeomorph hHolomorphicAlgebraicity A B g x
  have hcover : ft ≫ SingularPeriodsD.Constructions.SingularPeriods.projection (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) = SingularPeriodsD.Constructions.SingularPeriods.projection (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) ≫ gt := by
    apply TopCat.ext
    intro v
    exact (hlift v).symm
  have hp := congrArg (fun k => AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) k 1) hnative
  rw [AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp] at hp
  have hpc := ConcreteCategory.congr_hom hp c
  change AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) qB 1
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) gn 1 c) =
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) gt 1
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) qA 1 c) at hpc
  apply LatticePeriod.Constructions.LatticeDual.characterRestriction_injective (K := ℚ) (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B)
  ext ℓ
  let k : AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A := ⟨f (ℓ : Transport.Constructions.AbelianModel B), hf (ℓ : Transport.Constructions.AbelianModel B) ℓ.property⟩
  have hk : fQ (LatticePeriod.Constructions.LatticeDual.latticeInclusion (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) ℓ) = LatticePeriod.Constructions.LatticeDual.latticeInclusion (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) k := by
    apply Subtype.ext
    exact hfQ _
  change AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity B (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) gn 1 c)
      (LatticePeriod.Constructions.LatticeDual.latticeInclusion (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) ℓ) =
    AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A c (fQ (LatticePeriod.Constructions.LatticeDual.latticeInclusion (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) ℓ))
  erw [rationalH1Equiv_lattice hHolomorphicAlgebraicity B _ ℓ, hk, rationalH1Equiv_lattice hHolomorphicAlgebraicity A c k]
  rw [hpc]
  exact LatticePeriod.Constructions.PeriodNaturality.cohomologyPeriod_naturality
    (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ft gt hcover (map_zero f)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) qA 1 c) ℓ k rfl

end AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicPeriodNaturality

namespace AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions

/-!
# DegreeTwo: algebraicity of actual rational Hodge maps in weight one

The proof constructs the native exponential torus, identifies its singular H¹
and canonical Hodge pieces by actual lattice periods, applies the proved BettiLattice
correspondence, and uses the explicit HolomorphicAlgebraicity algebraization input. Construction and HodgeComparison are
used only as their named prerequisite propositions supplying canonical H¹
structures. The resulting pullback is the actual singular-cohomology map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj
open scoped TensorProduct _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps
  IntrinsicPeriodNaturality

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.Smooth A.toOver.hom := A.variety.presentation.smooth

/-- The full weight-one clause of the committed DegreeTwo statement, conditional
only on the explicit HolomorphicAlgebraicity, Construction, and HodgeComparison prerequisite propositions. -/
theorem weight_one_algebraicity
    (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (hConstruction : Transport.Constructions.ConstructionInput) (hHodgeComparison : Transport.Constructions.HodgeComparisonInput)
    (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (u : A.variety.rationalCohomology 1 →ₗ[ℚ] B.variety.rationalCohomology 1)
    (hu10 : ∀ x ∈ A.h1Holomorphic, u.baseChange ℂ x ∈ B.h1Holomorphic)
    (_hu01 : ∀ x ∈ A.h1Antiholomorphic, u.baseChange ℂ x ∈ B.h1Antiholomorphic) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : B.toOver ⟶ A.toOver,
      IsMonHom g ∧ ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g = (n : ℚ) • u := by
  obtain ⟨HA, hHA⟩ := Transport.Constructions.exists_canonicalH1 hConstruction hHodgeComparison A.variety η[A.toOver]
  obtain ⟨HB, hHB⟩ := Transport.Constructions.exists_canonicalH1 hConstruction hHodgeComparison B.variety η[B.toOver]
  have hu : ComplexMultiplication.WeightOne.CM.IsHodgeMap HA HB u := by
    intro x hx
    rw [hHA.1] at hx
    rw [hHB.1]
    exact hu10 x hx
  let eA := AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A
  let eB := AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity B
  let uL : (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A).H1Q →ₗ[ℚ] (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity B).H1Q :=
    eB.toLinearMap.comp (u.comp eA.symm.toLinearMap)
  have he : eB.symm.toLinearMap.comp uL = u.comp eA.symm.toLinearMap := by
    ext c
    exact eB.symm_apply_apply (u (eA.symm c))
  have heC (x : ComplexMultiplication.WeightOne.CM.Complexification (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A).H1Q) :
      eB.symm.toLinearMap.baseChange ℂ (uL.baseChange ℂ x) =
        u.baseChange ℂ (eA.symm.toLinearMap.baseChange ℂ x) := by
    calc
      _ = (eB.symm.toLinearMap.comp uL).baseChange ℂ x :=
        (LinearMap.congr_fun (LinearMap.baseChange_comp (A := ℂ)
          (f := uL) eB.symm.toLinearMap) x).symm
      _ = (u.comp eA.symm.toLinearMap).baseChange ℂ x :=
        congrArg (fun f => f.baseChange ℂ x) he
      _ = _ := LinearMap.congr_fun (LinearMap.baseChange_comp (A := ℂ)
        (f := eA.symm.toLinearMap) u) x
  have huL : ComplexMultiplication.WeightOne.CM.IsHodgeMap (TorusModel.Constructions.abelianH1Model hHolomorphicAlgebraicity A HA hHA).hodge
      (TorusModel.Constructions.abelianH1Model hHolomorphicAlgebraicity B HB hHB).hodge uL := by
    intro x hx
    change eA.symm.toLinearMap.baseChange ℂ x ∈ HA.holomorphic at hx
    change eB.symm.toLinearMap.baseChange ℂ (uL.baseChange ℂ x) ∈ HB.holomorphic
    rw [heC]
    exact hu _ hx
  obtain ⟨n, hn, g, ⟨hg, f, fQ, hf, hlift, hfQ, hpull⟩, _⟩ :=
    (Geometry.ComplexTorus.BettiLattice.CM.Construction.rational_hodge_description (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity B) (TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A)
      (TorusModel.Constructions.abelianH1Model hHolomorphicAlgebraicity B HB hHB) (TorusModel.Constructions.abelianH1Model hHolomorphicAlgebraicity A HA hHA) uL).mp huL
  obtain ⟨a, ha, hapull⟩ := Transport.Constructions.holomorphic_h1_algebraicity hHolomorphicAlgebraicity A B
    (IntrinsicTorusMaps.nativeMap hHolomorphicAlgebraicity A B g) (IntrinsicTorusMaps.nativeMap_mdifferentiable hHolomorphicAlgebraicity A B g hg)
  refine ⟨n, hn, a, ha, ?_⟩
  rw [hapull]
  apply LinearMap.ext
  intro c
  apply eB.injective
  have hp := IntrinsicPeriodNaturality.rationalH1Equiv_nativeMap_pullback hHolomorphicAlgebraicity A B g hg f fQ hf hlift hfQ c
  change eB
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨IntrinsicTorusMaps.nativeMap hHolomorphicAlgebraicity A B g,
        (IntrinsicTorusMaps.nativeMap_mdifferentiable hHolomorphicAlgebraicity A B g hg).continuous⟩) 1 c) = _
  rw [hp]
  erw [hpull (eA c)]
  change (n : ℚ) • eB (u (eA.symm (eA c))) = eB ((n : ℚ) • u c)
  erw [eA.symm_apply_apply, map_smul]

end AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions

end

end OAI
