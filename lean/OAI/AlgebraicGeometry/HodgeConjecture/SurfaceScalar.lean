import OAI.AlgebraicGeometry.HodgeConjecture.TopTrace
import OAI.AlgebraicGeometry.HodgeConjecture.Connected
import OAI.AlgebraicGeometry.HodgeConjecture.Projection
import OAI.AlgebraicGeometry.HodgeConjecture.CanonicalCoefficients

/-! # Surface Scalar -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.SurfaceScalar.CM.Construction

noncomputable section

/-! Integration along the surface factor is nonzero in the exact native
pushforward used by the correspondence. Connectedness and Kunneth prove
this without imposing a tensor-contraction formula as a hypothesis. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

def surfaceTraceMap (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (hS : S.complexDimension = 2) :
    S.rationalCohomology 4 →ₗ[ℚ] X.rationalCohomology 0 :=
  (Cycles.Functoriality.UnitCap.cohomologyPushforward (X := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
    (snd S.toOver X.toOver)
    (SurfaceConstructionQ.CM.map_isProper (S := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X) (X := X)
      (snd S.toOver X.toOver)) 2 0 (by rw [Products.CM.SurfaceConstruction.product_complexDimension, hS]; omega)).comp
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 4 (fst S.toOver X.toOver)).hom

theorem surfaceTraceMap_ne_zero (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace S.analyticSpace] [PathConnectedSpace X.analyticSpace]
    (hS : S.complexDimension = 2) (a : S.rationalCohomology 4) (ha : a ≠ 0) :
    surfaceTraceMap S X hS a ≠ 0 := by
  let W := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X
  let : PathConnectedSpace W.analyticSpace := Connected.CM.SurfaceConstruction.projectiveProduct_pathConnected S X
  have hd : W.complexDimension = X.complexDimension + 2 := by
    rw [Products.CM.SurfaceConstruction.product_complexDimension, hS, Nat.add_comm]
  obtain ⟨b, hb⟩ := TopTrace.CM.SurfaceConstruction.rationalTop_exists_ne_zero X
  have hext := Kunneth.CM.SurfaceConstruction.rational_exteriorCup_ne_zero
    (X := X.presentation) (Y := S.presentation) (Z := W.presentation)
    (snd S.toOver X.toOver) (fst S.toOver X.toOver)
    (BinaryFan.isLimitFlip (tensorProductIsBinaryProduct S.toOver X.toOver))
    (2 * X.complexDimension) 4 b a hb ha
  have hp := IntersectionTheory.ProjectionFormula.Cohomology.Construction.pairing_pushforward
    (Poincare.CM.SurfaceConstruction.nativePoincareData W) (Poincare.CM.SurfaceConstruction.nativePoincareData X)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (snd S.toOver X.toOver))
    (a := 4) (b := 0) (r := 2 * X.complexDimension)
    (by omega) (by omega) (by omega) (by omega) b
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 4 (fst S.toOver X.toOver) a)
  erw [Poincare.CM.SurfaceConstruction.nativePushforward_eq_Functoriality (X := W) (Y := X)
    (snd S.toOver X.toOver) 2 0 _ (by omega)] at hp
  intro hz
  change Cycles.Functoriality.UnitCap.cohomologyPushforward (X := W) (snd S.toOver X.toOver)
    (SurfaceConstructionQ.CM.map_isProper (S := W) (X := X) (snd S.toOver X.toOver)) 2 0 _
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 4 (fst S.toOver X.toOver) a) = 0 at hz
  rw [hz] at hp
  have hleft : IntersectionTheory.ProjectionFormula.Cohomology.Construction.pairing (Poincare.CM.SurfaceConstruction.nativePoincareData X) (by omega) b
      (0 : X.rationalCohomology 0) = 0 := by
    simp [IntersectionTheory.ProjectionFormula.Cohomology.Construction.pairing]
  have hzpair := hp.symm.trans hleft
  apply hext
  apply TopTrace.CM.SurfaceConstruction.rationalTopIntegral_injective W (2 * X.complexDimension + 4) (by omega)
  exact hzpair.trans (map_zero _).symm

theorem surfaceTraceMap_injective (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace S.analyticSpace] [PathConnectedSpace X.analyticSpace]
    (hS : S.complexDimension = 2) : Function.Injective (surfaceTraceMap S X hS) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  by_contra hn
  exact surfaceTraceMap_ne_zero S X hS a hn ha

theorem coefficientH0_smul_unit (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) [PathConnectedSpace X.analyticSpace]
    (a : E ⊗[ℚ] X.rationalCohomology 0) :
    ∃ r : E, r • ((1 : E) ⊗ₜ[ℚ] Cycles.Functoriality.UnitCap.cohomologyUnit X) = a := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb =>
    obtain ⟨r, rfl⟩ := ha
    obtain ⟨s, rfl⟩ := hb
    exact ⟨r + s, add_smul _ _ _⟩
  | tmul r a =>
    obtain ⟨q, rfl⟩ := TopTrace.CM.SurfaceConstruction.rationalH0_smul_unit X a
    refine ⟨r * algebraMap ℚ E q, ?_⟩
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [TensorProduct.tmul_smul]
    exact congrArg (fun c : E => c ⊗ₜ[ℚ] Cycles.Functoriality.UnitCap.cohomologyUnit X)
      (show r * algebraMap ℚ E q = q • r by rw [Algebra.smul_def, mul_comm])

theorem coefficientSurfaceTrace_scalar (E : IntermediateField ℚ ℂ)
    (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace S.analyticSpace] [PathConnectedSpace X.analyticSpace]
    (hS : S.complexDimension = 2)
    (a : E ⊗[ℚ] S.rationalCohomology 4) (ha : a ≠ 0) :
    ∃ r : E, r ≠ 0 ∧
      (surfaceTraceMap S X hS).baseChange E a =
        r • ((1 : E) ⊗ₜ[ℚ] Cycles.Functoriality.UnitCap.cohomologyUnit X) := by
  have hinj : Function.Injective ((surfaceTraceMap S X hS).baseChange E) :=
    TensorProduct.map_injective_of_flat_flat (LinearMap.id : E →ₗ[ℚ] E)
      (surfaceTraceMap S X hS) Function.injective_id (surfaceTraceMap_injective S X hS)
  obtain ⟨r, hr⟩ := coefficientH0_smul_unit E X ((surfaceTraceMap S X hS).baseChange E a)
  refine ⟨r, ?_, hr.symm⟩
  intro hz
  rw [hz, zero_smul] at hr
  exact ha (hinj (hr.symm.trans (map_zero _).symm))

theorem coefficientSurfaceTrace_eq (E : IntermediateField ℚ ℂ)
    (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (hS : S.complexDimension = 2)
    (a : E ⊗[ℚ] S.rationalCohomology 4) :
    (surfaceTraceMap S X hS).baseChange E a =
      (Cycles.Functoriality.UnitCap.cohomologyPushforward (X := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
        (snd S.toOver X.toOver)
        (SurfaceConstructionQ.CM.map_isProper (S := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X) (X := X)
          (snd S.toOver X.toOver)) 2 0 (by rw [Products.CM.SurfaceConstruction.product_complexDimension, hS]; omega)).baseChange E
        (Projection.CM.SurfaceConstruction.coefficientPullback E (W := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
          (fst S.toOver X.toOver) 4 a) := by
  unfold surfaceTraceMap
  erw [LinearMap.baseChange_comp]
  rfl

theorem coefficientCup_unit_right (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) (a : E ⊗[ℚ] X.rationalCohomology n) :
    CoefficientCups.CM.SurfaceConstruction.coefficientCup E X n 0 a ((1 : E) ⊗ₜ[ℚ] Cycles.Functoriality.UnitCap.cohomologyUnit X) = a := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha, hb]
  | tmul r a =>
    simp only [CoefficientCups.CM.SurfaceConstruction.coefficientCup, Intersections.CM.SurfaceConstruction.extendBilinear_tmul, mul_one]
    exact congrArg (fun z => r ⊗ₜ[ℚ] z)
      (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_cupUnit (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace X.toOver)) a)

end

end OAI.AlgebraicGeometry.HodgeConjecture.SurfaceScalar.CM.Construction
