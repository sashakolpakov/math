import OAI.RepresentationTheory.Theta.Adelic.DataTheta
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior

/-! # Intrinsic Second Projection -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic

noncomputable section

/-! The literal order-two, twice alternating projection in the two
distinguished annihilator directions and the two multiplicity directions. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}

def slot (i r : Fin 2) : Adelic.BallGeometryData.FrameIndex A := (A.distinguished, i.succ, r)

def slotEmbedding (r : Fin 2) : IntrinsicExterior.Intrinsic.Tangent →L[ℂ] (Adelic.BallGeometryData.FrameIndex A → ℂ) :=
  (ContinuousLinearMap.proj 0).smulRight (Pi.single (slot (A := A) 0 r) 1) +
    (ContinuousLinearMap.proj 1).smulRight (Pi.single (slot (A := A) 1 r) 1)

def tensorEvaluation (u v : Adelic.BallGeometryData.FrameIndex A → ℂ) : Adelic.DataTheta.TaylorTensor (A := A) 2 →L[ℂ] ℂ where
  toFun T := T ![u, v]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def secondCoefficient : Adelic.DataTheta.TaylorTensor (A := A) 2 →L[ℂ] ℂ :=
  tensorEvaluation (slotEmbedding 0 ![1, 0]) (slotEmbedding 1 ![0, 1]) -
  tensorEvaluation (slotEmbedding 0 ![0, 1]) (slotEmbedding 1 ![1, 0]) -
  tensorEvaluation (slotEmbedding 1 ![1, 0]) (slotEmbedding 0 ![0, 1]) +
  tensorEvaluation (slotEmbedding 1 ![0, 1]) (slotEmbedding 0 ![1, 0])

def secondProjection : Adelic.DataTheta.TaylorTensor (A := A) 2 →L[ℂ] IntrinsicExterior.Intrinsic.TopCovector :=
  secondCoefficient.smulRight IntrinsicExterior.Intrinsic.area

def tensorBilinear (T : Adelic.DataTheta.TaylorTensor (A := A) 2) :
    (Adelic.BallGeometryData.FrameIndex A → ℂ) →L[ℂ] (Adelic.BallGeometryData.FrameIndex A → ℂ) →L[ℂ] ℂ :=
  (continuousMultilinearCurryFin1 ℂ (Adelic.BallGeometryData.FrameIndex A → ℂ) ℂ).toContinuousLinearEquiv.toContinuousLinearMap.comp T.curryLeft

theorem tensorBilinear_apply (T : Adelic.DataTheta.TaylorTensor (A := A) 2) (u v : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    tensorBilinear T u v = T ![u, v] := by
  change T (Fin.cons u (Fin.snoc 0 v)) = _
  congr 1
  ext i
  fin_cases i <;> rfl

theorem tensor_coordinates (T : Adelic.DataTheta.TaylorTensor (A := A) 2) (r s : Fin 2) (u v : IntrinsicExterior.Intrinsic.Tangent) :
    T ![slotEmbedding r u, slotEmbedding s v] =
      u 0 * v 0 * T ![slotEmbedding r ![1, 0], slotEmbedding s ![1, 0]] +
      u 0 * v 1 * T ![slotEmbedding r ![1, 0], slotEmbedding s ![0, 1]] +
      u 1 * v 0 * T ![slotEmbedding r ![0, 1], slotEmbedding s ![1, 0]] +
      u 1 * v 1 * T ![slotEmbedding r ![0, 1], slotEmbedding s ![0, 1]] := by
  have he (t : Fin 2) (w : IntrinsicExterior.Intrinsic.Tangent) : slotEmbedding (A := A) t w =
      w 0 • slotEmbedding t ![1, 0] + w 1 • slotEmbedding t ![0, 1] := by
    simp [slotEmbedding]
  simp only [← tensorBilinear_apply, he r u, he s v, map_add, map_smul,
    _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-- Both antisymmetrizations are present. The source is the factorial-normalized
Taylor coefficient, so this four-term formula needs no further division. -/
theorem secondProjection_apply (T : Adelic.DataTheta.TaylorTensor (A := A) 2) (u v : IntrinsicExterior.Intrinsic.Tangent) :
    secondProjection T ![u, v] =
      T ![slotEmbedding 0 u, slotEmbedding 1 v] -
      T ![slotEmbedding 0 v, slotEmbedding 1 u] -
      T ![slotEmbedding 1 u, slotEmbedding 0 v] +
      T ![slotEmbedding 1 v, slotEmbedding 0 u] := by
  change (T ![slotEmbedding 0 ![1, 0], slotEmbedding 1 ![0, 1]] -
    T ![slotEmbedding 0 ![0, 1], slotEmbedding 1 ![1, 0]] -
    T ![slotEmbedding 1 ![1, 0], slotEmbedding 0 ![0, 1]] +
    T ![slotEmbedding 1 ![0, 1], slotEmbedding 0 ![1, 0]]) * IntrinsicExterior.Intrinsic.area ![u, v] = _
  rw [IntrinsicExterior.Intrinsic.area_apply]
  rw [tensor_coordinates T 0 1 u v, tensor_coordinates T 0 1 v u,
    tensor_coordinates T 1 0 u v, tensor_coordinates T 1 0 v u]
  ring

def thetaTopForm (B : Adelic.DataTheta.ComparisonData F H K A) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2))
    (z : Adelic.BallNatural.Ball) : IntrinsicExterior.Intrinsic.TopCovector := secondProjection (Adelic.DataTheta.geometricTensor B f 2 z)

theorem thetaTopForm_smooth (B : Adelic.DataTheta.ComparisonData F H K A)
    (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) :
    Adelic.BallGeometryData.BallSmooth (thetaTopForm B f) := by
  have h := hTheta.2.2.2.2.2 f 2
  unfold Adelic.BallGeometryData.BallSmooth at h ⊢
  have hc := (secondProjection (A := A)).restrictScalars ℝ |>.contDiff.comp_contDiffOn h
  apply hc.congr
  intro z hz
  simp [thetaTopForm, hz]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic
