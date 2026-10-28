import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.TopTrace
import OAI.AlgebraicGeometry.HodgeConjecture.Products

/-! # Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Projection.CM.Construction

noncomputable section

/-! Integration over an arbitrary connected projective factor. The map is
the native Functoriality pushforward, and its nonzero scalar is proved using Kunneth
and Poincare duality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CartesianMonoidalCategory
open scoped TensorProduct

open OAI.AlgebraicGeometry.HodgeConjecture.Products.CM.SurfaceConstruction

theorem projectiveProduct_pathConnected (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace S.analyticSpace] [PathConnectedSpace X.analyticSpace] :
    PathConnectedSpace (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X).analyticSpace := by
  let e := AlgebraicTopology.Kunneth.Add.Construction.productPointHomeomorph
    (Z := (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X).presentation)
    (fst S.toOver X.toOver) (snd S.toOver X.toOver) (tensorProductIsBinaryProduct _ _)
  exact e.symm.surjective.pathConnectedSpace e.symm.continuous

theorem native_pushforward_cast {W X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : W.toOver ⟶ X.toOver) (a a' b r : ℕ) (ha : a = a')
    (hW : a + r = 2 * W.complexDimension)
    (hW' : a' + r = 2 * W.complexDimension)
    (hX : b + r = 2 * X.complexDimension) (x : W.rationalCohomology a) :
    IntersectionTheory.ProjectionFormula.Definitions.pushforward (Poincare.CM.Construction.nativePoincareData W) (Poincare.CM.Construction.nativePoincareData X)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) a' b r hW' hX
      (cast (congrArg (fun n => (W.rationalCohomology n : Type)) ha) x) =
    IntersectionTheory.ProjectionFormula.Definitions.pushforward (Poincare.CM.Construction.nativePoincareData W) (Poincare.CM.Construction.nativePoincareData X)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) a b r hW hX x := by
  subst a'
  rfl

theorem native_projection_top {W X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : W.toOver ⟶ X.toOver) (d p : ℕ)
    (hdim : W.complexDimension = X.complexDimension + d)
    (hp : p ≤ X.complexDimension)
    (a : X.rationalCohomology (p + p)) (b : W.rationalCohomology (d + d)) :
    Cycles.Functoriality.UnitCap.cohomologyPushforward f (SurfaceConstructionQ.CM.map_isProper f) (p + d) p (by omega)
      (cast (congrArg (fun n => (W.rationalCohomology n : Type))
        (add_add_add_comm p p d d))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace W.toOver) (p + p) (d + d)
          (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f a) b)) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) (p + p) 0 a
        (Cycles.Functoriality.UnitCap.cohomologyPushforward f (SurfaceConstructionQ.CM.map_isProper f) d 0 (by omega) b) := by
  let : CompactSpace (Betti.Scheme.schemePointSpace W.toOver) := inferInstanceAs (CompactSpace W.analyticSpace)
  let : CompactSpace (Betti.Scheme.schemePointSpace X.toOver) := inferInstanceAs (CompactSpace X.analyticSpace)
  let : T2Space (Betti.Scheme.schemePointSpace W.toOver) := inferInstanceAs (T2Space W.analyticSpace)
  let : T2Space (Betti.Scheme.schemePointSpace X.toOver) := inferInstanceAs (T2Space X.analyticSpace)
  have h := IntersectionTheory.ProjectionFormula.Chow.Construction.projection_formula (Poincare.CM.Construction.nativePoincareData W) (Poincare.CM.Construction.nativePoincareData X)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) (p + p) (d + d) 0 (2 * X.complexDimension)
      (2 * (X.complexDimension - p))
    (by omega) (by omega) (by omega) (by omega) a b
  rw [← native_pushforward_cast f _ ((p + d) + (p + d)) _ _
    (add_add_add_comm p p d d) _ (by omega)] at h
  erw [Poincare.CM.Construction.nativePushforward_eq_Functoriality f (p + d) p _ (by omega),
    Poincare.CM.Construction.nativePushforward_eq_Functoriality f d 0 _ (by omega)] at h
  exact h

def factorTraceMap (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    S.rationalCohomology (S.complexDimension + S.complexDimension) →ₗ[ℚ]
      X.rationalCohomology 0 :=
  (Cycles.Functoriality.UnitCap.cohomologyPushforward (X := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
    (snd S.toOver X.toOver)
    (SurfaceConstructionQ.CM.map_isProper (S := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X) (X := X)
      (snd S.toOver X.toOver)) S.complexDimension 0
        (by rw [Products.CM.SurfaceConstruction.product_complexDimension]; omega)).comp
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ)
      (S.complexDimension + S.complexDimension) (fst S.toOver X.toOver)).hom

theorem factorTraceMap_ne_zero (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace S.analyticSpace] [PathConnectedSpace X.analyticSpace]
    (a : S.rationalCohomology (S.complexDimension + S.complexDimension)) (ha : a ≠ 0) :
    factorTraceMap S X a ≠ 0 := by
  let W := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X
  let : PathConnectedSpace W.analyticSpace := projectiveProduct_pathConnected S X
  have hd : W.complexDimension = X.complexDimension + S.complexDimension := by
    rw [Products.CM.SurfaceConstruction.product_complexDimension, Nat.add_comm]
  obtain ⟨b, hb⟩ := TopTrace.CM.Construction.rationalTop_exists_ne_zero X
  have hext := Kunneth.CM.SurfaceConstruction.rational_exteriorCup_ne_zero
    (X := X.presentation) (Y := S.presentation) (Z := W.presentation)
    (snd S.toOver X.toOver) (fst S.toOver X.toOver)
    (BinaryFan.isLimitFlip (tensorProductIsBinaryProduct S.toOver X.toOver))
    (2 * X.complexDimension) (S.complexDimension + S.complexDimension) b a hb ha
  have hp := IntersectionTheory.ProjectionFormula.Cohomology.Construction.pairing_pushforward
    (Poincare.CM.Construction.nativePoincareData W) (Poincare.CM.Construction.nativePoincareData X)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (snd S.toOver X.toOver))
    (a := S.complexDimension + S.complexDimension) (b := 0) (r := 2 * X.complexDimension)
    (by omega) (by omega) (by omega) (by omega) b
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) _ (fst S.toOver X.toOver) a)
  erw [Poincare.CM.Construction.nativePushforward_eq_Functoriality (X := W) (Y := X)
    (snd S.toOver X.toOver) S.complexDimension 0 _ (by omega)] at hp
  intro hz
  change Cycles.Functoriality.UnitCap.cohomologyPushforward (X := W) (snd S.toOver X.toOver)
    (SurfaceConstructionQ.CM.map_isProper (S := W) (X := X) (snd S.toOver X.toOver)) S.complexDimension 0 _
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) _ (fst S.toOver X.toOver) a) = 0 at hz
  rw [hz] at hp
  have hleft : IntersectionTheory.ProjectionFormula.Cohomology.Construction.pairing (Poincare.CM.Construction.nativePoincareData X) (by omega) b
      (0 : X.rationalCohomology 0) = 0 := by simp [IntersectionTheory.ProjectionFormula.Cohomology.Construction.pairing]
  have hzpair := hp.symm.trans hleft
  apply hext
  apply TopTrace.CM.Construction.rationalTopIntegral_injective W
    (2 * X.complexDimension + (S.complexDimension + S.complexDimension)) (by omega)
  exact hzpair.trans (map_zero _).symm

theorem factorTraceMap_injective (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace S.analyticSpace] [PathConnectedSpace X.analyticSpace] :
    Function.Injective (factorTraceMap S X) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  by_contra hn
  exact factorTraceMap_ne_zero S X a hn ha

theorem coefficient_factorTrace_scalar (K : Type) [Field K] [Algebra ℚ K]
    (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace S.analyticSpace] [PathConnectedSpace X.analyticSpace]
    (a : K ⊗[ℚ] S.rationalCohomology (S.complexDimension + S.complexDimension))
    (ha : a ≠ 0) :
    ∃ r : K, r ≠ 0 ∧ (factorTraceMap S X).baseChange K a =
      r • ((1 : K) ⊗ₜ[ℚ] Cycles.Functoriality.UnitCap.cohomologyUnit X) := by
  have hinj : Function.Injective ((factorTraceMap S X).baseChange K) :=
    TensorProduct.map_injective_of_flat_flat (LinearMap.id : K →ₗ[ℚ] K)
      (factorTraceMap S X) Function.injective_id (factorTraceMap_injective S X)
  have hunit : ∀ b : K ⊗[ℚ] X.rationalCohomology 0,
      ∃ r : K, r • ((1 : K) ⊗ₜ[ℚ] Cycles.Functoriality.UnitCap.cohomologyUnit X) = b := by
    intro b
    induction b using TensorProduct.inductionOn with
    | add b c hb hc =>
      obtain ⟨r, rfl⟩ := hb
      obtain ⟨s, rfl⟩ := hc
      exact ⟨r + s, add_smul _ _ _⟩
    | tmul r b =>
      obtain ⟨q, rfl⟩ := TopTrace.CM.Construction.rationalH0_smul_unit X b
      refine ⟨r * algebraMap ℚ K q, ?_⟩
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [TensorProduct.tmul_smul]
      exact congrArg (fun c : K => c ⊗ₜ[ℚ] Cycles.Functoriality.UnitCap.cohomologyUnit X)
        (show r * algebraMap ℚ K q = q • r by rw [Algebra.smul_def, mul_comm])
  obtain ⟨r, hr⟩ := hunit ((factorTraceMap S X).baseChange K a)
  refine ⟨r, ?_, hr.symm⟩
  intro hz
  rw [hz, zero_smul] at hr
  exact ha (hinj (hr.symm.trans (map_zero _).symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Projection.CM.Construction
