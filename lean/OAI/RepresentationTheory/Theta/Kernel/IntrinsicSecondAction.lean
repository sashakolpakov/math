import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection
import OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice

/-! # Intrinsic Second Action -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.Intrinsic

/-! Actual ball differential covariance of the twice alternating,
multiplicity-two completed theta tensor. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.Matrix

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.RepresentationTheory.Theta.Adelic.AnnihilatorFrame
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (B : Adelic.DataTheta.ComparisonData F H K A)

theorem frame_slot_row (hGeometry : Adelic.DataTheta.GeometryIdentification B)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball) (i r : Fin 2) (q : Adelic.BallGeometryData.FrameIndex A) :
    Adelic.BallGeometryData.frameMatrix A g z (IntrinsicSecondProjection.Intrinsic.slot (A := A) i r) q =
      if q = IntrinsicSecondProjection.Intrinsic.slot (A := A) 0 r then Adelic.DeterminantCoordinates.dualCoordinates (Adelic.BallNatural.asSL (B.ball g)) z.val i 0
      else if q = IntrinsicSecondProjection.Intrinsic.slot (A := A) 1 r then Adelic.DeterminantCoordinates.dualCoordinates (Adelic.BallNatural.asSL (B.ball g)) z.val i 1
      else 0 := by
  have hinv : (Adelic.BallGeometryData.standardMatrix A g A.distinguished)⁻¹ = ((Adelic.BallNatural.asSL (B.ball g))⁻¹).val := by
    rw [← hGeometry.2.1 g, Matrix.inv_def, (Adelic.BallNatural.asSL (B.ball g)).property]
    simp [Matrix.SpecialLinearGroup.coe_inv]
  rcases q with ⟨v, j, k⟩
  fin_cases i <;> fin_cases j <;>
    by_cases hv : v = A.distinguished <;> by_cases hk : k = r
  all_goals
    simp [Adelic.BallGeometryData.frameMatrix, Adelic.BallGeometryData.geometricCoordinates, Adelic.BallGeometryData.geometricAction, Adelic.BallGeometryData.geometricFrame,
      IntrinsicSecondProjection.Intrinsic.slot, hinv, Adelic.DeterminantCoordinates.dualCoordinates, Adelic.DeterminantCoordinates.dualColumn, Adelic.DeterminantCoordinates.annihilatorVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, hv, hk, Ne.symm, Pi.single_apply]

theorem frame_transpose_embedding (hGeometry : Adelic.DataTheta.GeometryIdentification B)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball) (r : Fin 2) (u : Fin 2 → ℂ) :
    (Adelic.BallGeometryData.frameMatrix A g z).transpose.mulVec (IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := A) r u) =
      IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := A) r
        ((Adelic.DeterminantCoordinates.dualCoordinates (Adelic.BallNatural.asSL (B.ball g)) z.val).transpose.mulVec u) := by
  funext q
  change ((Adelic.BallGeometryData.frameMatrix A g z).transpose.mulVec
    (u 0 • Pi.single (IntrinsicSecondProjection.Intrinsic.slot (A := A) 0 r) 1 + u 1 • Pi.single (IntrinsicSecondProjection.Intrinsic.slot (A := A) 1 r) 1)) q = _
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.mulVec_single, MulOpposite.op_one,
    one_smul, Matrix.col, Matrix.transpose_apply, smul_eq_mul]
  rw [frame_slot_row B hGeometry g z 0 r q, frame_slot_row B hGeometry g z 1 r q]
  by_cases hq0 : q = IntrinsicSecondProjection.Intrinsic.slot (A := A) 0 r
  · subst q
    simp [IntrinsicSecondProjection.Intrinsic.slotEmbedding, IntrinsicSecondProjection.Intrinsic.slot, mul_comm]
  · by_cases hq1 : q = IntrinsicSecondProjection.Intrinsic.slot (A := A) 1 r
    · subst q
      simp [IntrinsicSecondProjection.Intrinsic.slotEmbedding, IntrinsicSecondProjection.Intrinsic.slot, mul_comm]
    · simp [IntrinsicSecondProjection.Intrinsic.slotEmbedding, hq0, hq1]

theorem tensor_slot_covariance
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K) (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2)
    (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P)
    (hGeometry : Adelic.DataTheta.GeometryIdentification B) (hCovariance : Adelic.DataTheta.Descent.RationalHeckeCovariance B P hd C D)
    (g : Adelic.SpecialUnitary.SU H.val) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) (z : Adelic.BallNatural.Ball) (r s : Fin 2)
    (u v : Fin 2 → ℂ) :
    Adelic.DataTheta.geometricTensor B (Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f) 2
        (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)
        ![IntrinsicSecondProjection.Intrinsic.slotEmbedding r (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
            (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val u),
          IntrinsicSecondProjection.Intrinsic.slotEmbedding s (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
            (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val v)] =
      Adelic.DataTheta.geometricTensor B f 2 z ![IntrinsicSecondProjection.Intrinsic.slotEmbedding r u, IntrinsicSecondProjection.Intrinsic.slotEmbedding s v] := by
  let gA := Adelic.RationalSU.rationalArchimedeanSU F H g
  let gB := B.ball gA
  let M := Adelic.BallGeometryData.frameMatrix A gA z
  let w : Fin 2 → Fin 2 → ℂ := ![u, v]
  let t : Fin 2 → Fin 2 := ![r, s]
  let a (i : Fin 2) := M.transpose.mulVec
    (IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := A) (t i) (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL gB)) z.val (w i)))
  have hunit : IsUnit M.det := by
    apply isUnit_iff_ne_zero.mpr
    change (Adelic.BallGeometryData.frameMatrix A gA z).det ≠ 0
    rw [hGeometry.2.2.2.2.2.2.2.2.2.1, Adelic.DeterminantCoordinates.hodgeDeterminantFactor_eq]
    exact pow_ne_zero _ (pow_ne_zero 2 (Adelic.BallNatural.denominator_ne_zero gB z))
  have hcancel (i : Fin 2) : Adelic.BallGeometryData.dualFrameChange A gA z (a i) =
      IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := A) (t i) (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL gB)) z.val (w i)) := by
    unfold Adelic.BallGeometryData.dualFrameChange a
    change M⁻¹ᵀ.mulVec (Mᵀ.mulVec _) = _
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv M hunit, Matrix.transpose_one, Matrix.one_mulVec]
  have harg (i : Fin 2) : Adelic.DeterminantCoordinates.denominator (Adelic.BallNatural.asSL gB) z.val • a i =
      IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := A) (t i) (w i) := by
    dsimp [a]
    rw [frame_transpose_embedding B hGeometry]
    rw [← map_smul, OneFormsIntrinsicLattice.IntrinsicCotangentAction.cotangent_derivative _ _ _
      (Adelic.BallNatural.denominator_ne_zero gB z)]
  have hc := (hCovariance g f).2.2.2 2 z a
  have ha : (fun i => Adelic.BallGeometryData.dualFrameChange A gA z (a i)) =
      ![IntrinsicSecondProjection.Intrinsic.slotEmbedding r (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL gB)) z.val u),
        IntrinsicSecondProjection.Intrinsic.slotEmbedding s (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL gB)) z.val v)] := by
    funext i
    rw [hcancel]
    fin_cases i <;> rfl
  change Adelic.DataTheta.geometricTensor B _ 2 (gB • z)
    (fun i => Adelic.BallGeometryData.dualFrameChange A gA z (a i)) = _ at hc
  rw [ha] at hc
  rw [hc]
  have he := (Adelic.DataTheta.geometricTensor B f 2 z).map_smul_univ
    (fun _ : Fin 2 => Adelic.DeterminantCoordinates.denominator (Adelic.BallNatural.asSL gB) z.val) a
  have hb : (fun i => Adelic.DeterminantCoordinates.denominator (Adelic.BallNatural.asSL gB) z.val • a i) =
      ![IntrinsicSecondProjection.Intrinsic.slotEmbedding r u, IntrinsicSecondProjection.Intrinsic.slotEmbedding s v] := by
    funext i
    rw [harg]
    fin_cases i <;> rfl
  rw [hb] at he
  simpa [Adelic.BallNatural.Factors.naturalHalfFactor, Adelic.BallNatural.Factors.automorphyFactor, Fin.prod_univ_two, pow_two] using he.symm

theorem thetaTopForm_covariance
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K) (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2)
    (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P)
    (hGeometry : Adelic.DataTheta.GeometryIdentification B) (hCovariance : Adelic.DataTheta.Descent.RationalHeckeCovariance B P hd C D)
    (g : Adelic.SpecialUnitary.SU H.val) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) (z : Adelic.BallNatural.Ball) :
    (IntrinsicSecondProjection.Intrinsic.thetaTopForm B (Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f)
      (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)).compContinuousLinearMap
        (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val) =
      IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z := by
  apply ContinuousAlternatingMap.ext
  intro w
  have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
  rw [hw]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change IntrinsicSecondProjection.Intrinsic.secondProjection (Adelic.DataTheta.geometricTensor B
    (Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f) 2
    (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z))
    ![fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val (w 0),
      fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val (w 1)] =
    IntrinsicSecondProjection.Intrinsic.secondProjection (Adelic.DataTheta.geometricTensor B f 2 z) ![w 0, w 1]
  rw [IntrinsicSecondProjection.Intrinsic.secondProjection_apply, IntrinsicSecondProjection.Intrinsic.secondProjection_apply]
  rw [tensor_slot_covariance B P hd C D hGeometry hCovariance,
    tensor_slot_covariance B P hd C D hGeometry hCovariance,
    tensor_slot_covariance B P hd C D hGeometry hCovariance,
    tensor_slot_covariance B P hd C D hGeometry hCovariance]

end RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.Intrinsic

namespace RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.IntrinsicTransport

/-! The order-two projection intertwines the actual geometric tensor
bundle relation and pullback of ordinary alternating top covectors. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.RepresentationTheory.Theta.Adelic.AnnihilatorFrame
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.Intrinsic
variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (B : Adelic.DataTheta.ComparisonData F H K A)

theorem tensor_slot_transport (hGeometry : Adelic.DataTheta.GeometryIdentification B)
    (gA : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball) (T Tnew : Adelic.DataTheta.TaylorTensor (A := A) 2)
    (hTransport : ∀ a, Tnew (fun i => Adelic.BallGeometryData.dualFrameChange A gA z (a i)) =
      Adelic.BallNatural.Factors.naturalHalfFactor 2 (B.ball gA) z * T a)
    (r s : Fin 2) (u v : Fin 2 → ℂ) :
    Tnew ![IntrinsicSecondProjection.Intrinsic.slotEmbedding r (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL (B.ball gA))) z.val u),
      IntrinsicSecondProjection.Intrinsic.slotEmbedding s (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL (B.ball gA))) z.val v)] =
    T ![IntrinsicSecondProjection.Intrinsic.slotEmbedding r u, IntrinsicSecondProjection.Intrinsic.slotEmbedding s v] := by
  let gB := B.ball gA
  let M := Adelic.BallGeometryData.frameMatrix A gA z
  let w : Fin 2 → Fin 2 → ℂ := ![u, v]
  let t : Fin 2 → Fin 2 := ![r, s]
  let a (i : Fin 2) := M.transpose.mulVec
    (IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := A) (t i) (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL gB)) z.val (w i)))
  have hunit : IsUnit M.det := by
    apply isUnit_iff_ne_zero.mpr
    change (Adelic.BallGeometryData.frameMatrix A gA z).det ≠ 0
    rw [hGeometry.2.2.2.2.2.2.2.2.2.1, Adelic.DeterminantCoordinates.hodgeDeterminantFactor_eq]
    exact pow_ne_zero _ (pow_ne_zero 2 (Adelic.BallNatural.denominator_ne_zero gB z))
  have hcancel (i : Fin 2) : Adelic.BallGeometryData.dualFrameChange A gA z (a i) =
      IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := A) (t i) (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL gB)) z.val (w i)) := by
    unfold Adelic.BallGeometryData.dualFrameChange a
    change M⁻¹ᵀ.mulVec (Mᵀ.mulVec _) = _
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv M hunit, Matrix.transpose_one, Matrix.one_mulVec]
  have harg (i : Fin 2) : Adelic.DeterminantCoordinates.denominator (Adelic.BallNatural.asSL gB) z.val • a i =
      IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := A) (t i) (w i) := by
    dsimp [a]
    rw [Intrinsic.frame_transpose_embedding B hGeometry]
    rw [← map_smul, OneFormsIntrinsicLattice.IntrinsicCotangentAction.cotangent_derivative _ _ _
      (Adelic.BallNatural.denominator_ne_zero gB z)]
  have hc := hTransport a
  have ha : (fun i => Adelic.BallGeometryData.dualFrameChange A gA z (a i)) =
      ![IntrinsicSecondProjection.Intrinsic.slotEmbedding r (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL gB)) z.val u),
        IntrinsicSecondProjection.Intrinsic.slotEmbedding s (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL gB)) z.val v)] := by
    funext i
    rw [hcancel]
    fin_cases i <;> rfl
  change Tnew
    (fun i => Adelic.BallGeometryData.dualFrameChange A gA z (a i)) = _ at hc
  rw [ha] at hc
  rw [hc]
  have he := (T).map_smul_univ
    (fun _ : Fin 2 => Adelic.DeterminantCoordinates.denominator (Adelic.BallNatural.asSL gB) z.val) a
  have hb : (fun i => Adelic.DeterminantCoordinates.denominator (Adelic.BallNatural.asSL gB) z.val • a i) =
      ![IntrinsicSecondProjection.Intrinsic.slotEmbedding r u, IntrinsicSecondProjection.Intrinsic.slotEmbedding s v] := by
    funext i
    rw [harg]
    fin_cases i <;> rfl
  rw [hb] at he
  simpa [Adelic.BallNatural.Factors.naturalHalfFactor, Adelic.BallNatural.Factors.automorphyFactor, Fin.prod_univ_two, pow_two] using he.symm

theorem secondProjection_transport (hGeometry : Adelic.DataTheta.GeometryIdentification B)
    (gA : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball) (T Tnew : Adelic.DataTheta.TaylorTensor (A := A) 2)
    (hTransport : ∀ a, Tnew (fun i => Adelic.BallGeometryData.dualFrameChange A gA z (a i)) =
      Adelic.BallNatural.Factors.naturalHalfFactor 2 (B.ball gA) z * T a) :
    (IntrinsicSecondProjection.Intrinsic.secondProjection Tnew).compContinuousLinearMap
      (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL (B.ball gA))) z.val) = IntrinsicSecondProjection.Intrinsic.secondProjection T := by
  apply ContinuousAlternatingMap.ext
  intro w
  have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
  rw [hw]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change IntrinsicSecondProjection.Intrinsic.secondProjection Tnew
    ![fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL (B.ball gA))) z.val (w 0),
      fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL (B.ball gA))) z.val (w 1)] =
    IntrinsicSecondProjection.Intrinsic.secondProjection T ![w 0, w 1]
  rw [IntrinsicSecondProjection.Intrinsic.secondProjection_apply, IntrinsicSecondProjection.Intrinsic.secondProjection_apply]
  rw [tensor_slot_transport B hGeometry gA z T Tnew hTransport,
    tensor_slot_transport B hGeometry gA z T Tnew hTransport,
    tensor_slot_transport B hGeometry gA z T Tnew hTransport,
    tensor_slot_transport B hGeometry gA z T Tnew hTransport]

end RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.IntrinsicTransport

end

end OAI
