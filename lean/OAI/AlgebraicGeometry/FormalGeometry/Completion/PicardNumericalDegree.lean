import OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundleHilbertCoefficients
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GeneratedAmpleBundle

/-! # Picard Numerical Degree -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PicardNumericalDegree

noncomputable section

/-! The next-to-leading Hilbert coefficient defines an additive numerical
degree on the actual Picard group of an integral closed projective scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Polynomial

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

variable {K : Type u} [Field K] {r : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion f]

theorem lineBundleHilbertDifference_natDegree_le (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) :
    (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f L j).natDegree ≤
      (EffectiveHilbertDifference.Construction.lineBundleHilbertPolynomial f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X) j).natDegree - 1 := by
  by_cases h : EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f L j = 0
  · simp only [h, natDegree_zero, Nat.zero_le]
  · have hd := natDegree_lt_natDegree h (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference_degree_lt f L j)
    omega

def lineBundleNumericalDegree (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) : ℚ :=
  LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient f L j
    ((EffectiveHilbertDifference.Construction.lineBundleHilbertPolynomial f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X) j).natDegree - 1)

omit [IsIntegral X] in
theorem lineBundleNumericalDegree_iso (L B : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (e : L.sheaf ≅ B.sheaf)
    (j : Fin (r + 1)) : lineBundleNumericalDegree f L j = lineBundleNumericalDegree f B j :=
  LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient_iso f L B e j _

omit [IsIntegral X] in
theorem lineBundleNumericalDegree_trivial (j : Fin (r + 1)) :
    lineBundleNumericalDegree f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X) j = 0 := by
  unfold lineBundleNumericalDegree LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient EffectiveHilbertDifference.Construction.lineBundleHilbertDifference
  rw [sub_self, coeff_zero]

theorem lineBundleNumericalDegree_tensor_generated_left [Infinite K]
    (B L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hB : Frame.SectionDetection.Construction.HasFrameSections B.sheaf) (j : Fin (r + 1)) :
    lineBundleNumericalDegree f (B.tensor L) j =
      lineBundleNumericalDegree f B j + lineBundleNumericalDegree f L j :=
  LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient_tensor_generated_left f B L hB j _
    (lineBundleHilbertDifference_natDegree_le f B j)

theorem lineBundleNumericalDegree_tensor [Infinite K] (B L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) :
    lineBundleNumericalDegree f (B.tensor L) j =
      lineBundleNumericalDegree f B j + lineBundleNumericalDegree f L j := by
  obtain ⟨n, hn⟩ := Projective.SectionGeneration.Construction.closedProjectiveLineBundleTwist_eventually_hasFrameSections f B j
  let P := (Frame.SectionDetection.Construction.coordinatePositiveTwist_hasFrameSections (R := K) j n).lineBundle
  let T := P.pullback f
  have hT : Frame.SectionDetection.Construction.HasFrameSections T.sheaf :=
    (Frame.SectionDetection.Construction.coordinatePositiveTwist_hasFrameSections (R := K) j n).pullback f
  have hBT : Frame.SectionDetection.Construction.HasFrameSections (B.tensor T).sheaf :=
    (hn n le_rfl).of_iso (Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.tensorIso B.sheaf T.sheaf)
  have h₁ := lineBundleNumericalDegree_tensor_generated_left f (B.tensor T) L hBT j
  have h₂ := lineBundleNumericalDegree_tensor_generated_left f T B hT j
  have h₃ := lineBundleNumericalDegree_tensor_generated_left f T (B.tensor L) hT j
  have he₂ : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (B.tensor T) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (T.tensor B) :=
    mul_comm (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf T)
  have he₁ : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((B.tensor T).tensor L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (T.tensor (B.tensor L)) :=
    (mul_assoc (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).trans
      (mul_left_comm (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
  obtain ⟨e₁⟩ := Quotient.exact he₁
  obtain ⟨e₂⟩ := Quotient.exact he₂
  rw [lineBundleNumericalDegree_iso f _ _ e₁ j, lineBundleNumericalDegree_iso f _ _ e₂ j] at h₁
  linarith

def picardNumericalDegreeValue (j : Fin (r + 1)) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X → ℚ :=
  Quotient.lift (fun L => lineBundleNumericalDegree f L j)
    (fun L B ⟨e⟩ => lineBundleNumericalDegree_iso f L B e j)

theorem picardNumericalDegreeValue_mul [Infinite K] (j : Fin (r + 1))
    (q t : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    picardNumericalDegreeValue f j (q * t) = picardNumericalDegreeValue f j q + picardNumericalDegreeValue f j t := by
  induction q using Quotient.inductionOn with
  | h L =>
    induction t using Quotient.inductionOn with
    | h B => exact lineBundleNumericalDegree_tensor f L B j

def picardNumericalDegree [Infinite K] (j : Fin (r + 1)) : Additive (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) →+ ℚ where
  toFun q := picardNumericalDegreeValue f j q.toMul
  map_zero' := lineBundleNumericalDegree_trivial f j
  map_add' q t := picardNumericalDegreeValue_mul f j q.toMul t.toMul

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PicardNumericalDegree
