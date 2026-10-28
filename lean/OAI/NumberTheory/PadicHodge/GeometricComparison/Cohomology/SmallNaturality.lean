import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.CrystallineComparison
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.SmallPullbackDefinition

/-! # Small Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The Cohomology and GeometricComparison ordinary crystalline pullbacks agree under the actual special-fiber identification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Cohomology.SmallNaturality.equalModule_operator_square {I : Type*} {R : Type*} [Ring R]
    (C : I → ModuleCat R) (T : ∀ i, C i →ₗ[R] C i) {i j : I} (h : i = j) (x : C i) :
    (eqToIso (congrArg C h)).toLinearEquiv (T i x) =
      T j ((eqToIso (congrArg C h)).toLinearEquiv x) := by
  subst j
  rfl

theorem Cohomology.SmallNaturality.equalModule_operator_square_linear {I : Type*} {R : Type*} [Ring R]
    (C : I → ModuleCat R) (T : ∀ i, C i →ₗ[R] C i) {i j : I} (h : i = j) :
    (eqToIso (congrArg C h)).toLinearEquiv.toLinearMap.comp (T i) =
      (T j).comp (eqToIso (congrArg C h)).toLinearEquiv.toLinearMap := by
  subst j
  rfl

namespace Cohomology.SmallNaturality.CrystallineAdapter

variable (q : ℕ) [Fact q.Prime]
  {X Y : Over (Spec (CommRingCat.of ℤ_[q]))} [IsProper X.hom] [IsProper Y.hom] (f : X ⟶ Y)

theorem smallPullback_eq_Cohomology :
    SmallCrystallineOperators.CrystallineAdapter.smallPullback q (AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.specialFiberMap (DVR.PadicBase.dvr q) f) =
      AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.crystallinePullback (DVR.PadicBase.dvr q) f 1 :=
  (CanonicalSmallPullback.CrystallineAdapter.smallPullback_eq_canonical q (AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.specialFiberMap (DVR.PadicBase.dvr q) f)).trans
    (SmallPullbackDefinition.CrystallineAdapter.canonicalSmallPullback_eq_Cohomology (DVR.PadicBase.dvr q) f 1)

end Cohomology.SmallNaturality.CrystallineAdapter

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.e62SmallEquiv_naturality (f : A.ExtendingEndomorphism) :
    A.e62SmallEquiv.toLinearMap.comp (A.smallCrystallinePullback f) =
      (AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.crystallinePullback (DVR.PadicBase.dvr q) f.integral.toMul.hom.hom 1).comp
        A.e62SmallEquiv.toLinearMap := by
  let : IsProper A.integral.scheme.hom := A.integral.proper
  let f0 : End A.integral.scheme := f.integral.toMul.hom.hom
  let C := fun r : ℤ_[q] →+* ZMod q =>
    AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology q (ZMod q)
      ((Over.pullback (Spec.map (CommRingCat.ofHom r))).obj A.integral.scheme) 1
  let T : ∀ r : ℤ_[q] →+* ZMod q, C r →ₗ[FractionRing (Crystalline.CoefficientAdapter.Witt q)] C r := fun r => by
    let : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom r))).obj A.integral.scheme).hom :=
      (A.integral.pullback (Spec.map (CommRingCat.ofHom r))).proper
    exact SmallCrystallineOperators.CrystallineAdapter.smallPullback q
      ((Over.pullback (Spec.map (CommRingCat.ofHom r))).map f0)
  have h := Cohomology.SmallNaturality.equalModule_operator_square_linear C T (DVR.PadicBase.reduction_eq q).symm
  exact h.trans (congrArg (fun t => t.comp A.e62SmallEquiv.toLinearMap)
    (Cohomology.SmallNaturality.CrystallineAdapter.smallPullback_eq_Cohomology q f0))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
