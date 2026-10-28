import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection
import OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice

/-! # Intrinsic Frame Entries -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameEntries.Intrinsic

noncomputable section

/-! Scalar entry formulas avoid changing the dependent arithmetic index
types while simplifying Hodge-frame and slot identities. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

def frameCoefficient (M : Matrix (Fin 3) (Fin 3) ℂ) (z : Adelic.BallNatural.Ball)
    (distinguished : Prop) [Decidable distinguished] (positive : Bool) (i j : Fin 3) : ℂ :=
  let p : Fin 3 → ℂ := fun k =>
    if distinguished then Adelic.DeterminantCoordinates.lineVector z.val k * (Pi.single j (1 : ℂ) : Fin 3 → ℂ) 0
    else if positive then (Pi.single j (1 : ℂ) : Fin 3 → ℂ) k else 0
  let q : Fin 3 → ℂ := fun k =>
    if distinguished then Adelic.DeterminantCoordinates.annihilatorVector z.val 0 k * (Pi.single j (1 : ℂ) : Fin 3 → ℂ) 1 +
      Adelic.DeterminantCoordinates.annihilatorVector z.val 1 k * (Pi.single j (1 : ℂ) : Fin 3 → ℂ) 2
    else if positive then 0 else (Pi.single j (1 : ℂ) : Fin 3 → ℂ) k
  if distinguished then
    if i = 0 then ∑ k, M 2 k * p k
    else if i = 1 then ∑ k, M⁻¹ k 0 * q k
    else ∑ k, M⁻¹ k 1 * q k
  else if positive then ∑ k, M i k * p k
  else ∑ k, M⁻¹ k i * q k

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}

theorem frameMatrix_entry (A : Adelic.BallGeometryData.BallArithmeticData F d m H K)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball) (v w : Fin A.places) (i j : Fin 3) (r s : Fin m) :
    Adelic.BallGeometryData.frameMatrix A g z (v,i,r) (w,j,s) =
      if v = w ∧ r = s then
        frameCoefficient (Adelic.BallGeometryData.standardMatrix A g v) z (v = A.distinguished) (A.positive v r) i j
      else 0 := by
  by_cases hv : v = w <;> by_cases hr : r = s
  · subst w
    subst s
    simp [Adelic.BallGeometryData.frameMatrix, Adelic.BallGeometryData.geometricCoordinates, Adelic.BallGeometryData.geometricAction, Adelic.BallGeometryData.geometricFrame,
      frameCoefficient, Pi.single_apply, Prod.mk.injEq]
  · simp [Adelic.BallGeometryData.frameMatrix, Adelic.BallGeometryData.geometricCoordinates, Adelic.BallGeometryData.geometricAction, Adelic.BallGeometryData.geometricFrame,
      Pi.single_apply, Prod.mk.injEq, hr]
  · simp [Adelic.BallGeometryData.frameMatrix, Adelic.BallGeometryData.geometricCoordinates, Adelic.BallGeometryData.geometricAction, Adelic.BallGeometryData.geometricFrame,
      Prod.mk.injEq, hv]
  · simp [Adelic.BallGeometryData.frameMatrix, Adelic.BallGeometryData.geometricCoordinates, Adelic.BallGeometryData.geometricAction, Adelic.BallGeometryData.geometricFrame,
      Prod.mk.injEq, hv]

theorem second_slot_apply
    {K₂ : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    (A₂ : Adelic.BallGeometryData.BallArithmeticData F d 2 H K₂) (r : Fin 2) (u : Fin 2 → ℂ) (q : Adelic.BallGeometryData.FrameIndex A₂) :
    IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := A₂) r u q =
      u 0 * (if q = (A₂.distinguished, 1, r) then 1 else 0) +
      u 1 * (if q = (A₂.distinguished, 2, r) then 1 else 0) := by
  simp [IntrinsicSecondProjection.Intrinsic.slotEmbedding, IntrinsicSecondProjection.Intrinsic.slot, Pi.single_apply]

theorem first_slot_apply
    {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    (A₁ : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁) (u : Fin 2 → ℂ) (q : Adelic.BallGeometryData.FrameIndex A₁) :
    OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding (A := A₁) u q =
      u 0 * (if q = (A₁.distinguished, 1, 0) then 1 else 0) +
      u 1 * (if q = (A₁.distinguished, 2, 0) then 1 else 0) := by
  simp [OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding, OneFormsIntrinsicLattice.IntrinsicProjection.slot, Pi.single_apply]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameEntries.Intrinsic
