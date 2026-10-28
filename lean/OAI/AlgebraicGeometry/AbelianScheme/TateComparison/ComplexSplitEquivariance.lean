import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalCompletion
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexPeriodAction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPELMaps
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Complex Split Equivariance -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianScheme.TateComparison

/-! Construct the split rational Tate frame of an actual complex PEL
fiber from its native period marking and its split number-field completion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s)

def Data.SphericalPELAlbaneseData.splitFieldCube : ℚ_[q] ⊗[ℚ] (Fin 3 → E) ≃ₗ[ℚ_[q]] Rational.SplitTateSpace s q :=
  (TensorProduct.piRight ℚ ℚ_[q] ℚ_[q] (fun _ : Fin 3 => E)).trans
    ((LinearEquiv.piCongrRight fun _ : Fin 3 => (D.rationalCompletionEquiv hg hdegree).toLinearEquiv).trans {
      toFun f v i := f i v
      invFun f i v := f v i
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl })

theorem Data.SphericalPELAlbaneseData.splitFieldCube_tmul (z : ℚ_[q]) (a : Fin 3 → E) (v : Fin s × Bool) (i : Fin 3) :
    D.splitFieldCube hg hdegree (z ⊗ₜ[ℚ] a) v i = z * D.rationalLocalCharacter v (a i) := rfl

def Data.SphericalPELAlbaneseData.splitPeriodFrame {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (c : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ≃ₗ[ℚ] (Fin 3 → E)) :
    Rational.SplitTateFrame s A.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q :=
  (IntrinsicPELMaps.pelRationalPeriodTateEquiv A P q).symm.trans
    ((LinearEquiv.baseChange ℚ ℚ_[q] _ _ c).trans (D.splitFieldCube hg hdegree))

end AlgebraicGeometry.AbelianScheme.TateComparison

namespace AlgebraicGeometry.AbelianScheme.TateComparison.ComplexSplitEquivariance.SphericalPELAlbaneseData

/-! The period frame respects the actual integral PEL action. Transport
along the equality of complex bases gives a compatible frame of the actual
geometric fiber without comparing expanded fiber-product constructions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (F : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation F.abelian.scheme.left F.abelian.scheme.hom)

private def periodCoordinatesQ : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native F.abelian P) ≃ₗ[ℚ] (Fin 3 → E) := by
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule F.abelian P (PELAdapters.actionFromEnd F.action)
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower F.abelian P (PELAdapters.actionFromEnd F.action)
  exact (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates F.abelian P (PELAdapters.actionFromEnd F.action)
    s hs rfl hdegree).restrictScalars ℚ

private theorem periodCoordinatesQ_integer (a : NumberField.RingOfIntegers E)
    (v : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native F.abelian P)) :
    periodCoordinatesQ D hdegree hs F P (AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction F.abelian P (PELAdapters.actionFromEnd F.action) a v) =
      (a : E) • periodCoordinatesQ D hdegree hs F P v := by
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule F.abelian P (PELAdapters.actionFromEnd F.action)
  rw [← AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply]
  change (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates F.abelian P (PELAdapters.actionFromEnd F.action) s hs rfl hdegree)
    ((a : E) • v) = _
  exact (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates F.abelian P (PELAdapters.actionFromEnd F.action)
    s hs rfl hdegree).map_smul (a : E) v

private theorem splitPeriodFrame_period (z : ℚ_[q]) (a : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native F.abelian P))
    (v : Fin s × Bool) (i : Fin 3) :
    D.splitPeriodFrame hg hdegree F.abelian P (periodCoordinatesQ D hdegree hs F P)
        (IntrinsicPELMaps.pelRationalPeriodTateEquiv F.abelian P q (z ⊗ₜ[ℚ] a)) v i =
      z * D.rationalLocalCharacter v (periodCoordinatesQ D hdegree hs F P a i) := by
  change D.splitFieldCube hg hdegree
    ((LinearEquiv.baseChange ℚ ℚ_[q] _ _ (periodCoordinatesQ D hdegree hs F P))
      ((IntrinsicPELMaps.pelRationalPeriodTateEquiv F.abelian P q).symm
        (IntrinsicPELMaps.pelRationalPeriodTateEquiv F.abelian P q (z ⊗ₜ[ℚ] a)))) v i = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul, Data.SphericalPELAlbaneseData.splitFieldCube_tmul]

private theorem splitPeriodFrame_action :
    Rational.IsSplitActionFrame F (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q D.localCharacter
      (D.splitPeriodFrame hg hdegree F.abelian P (periodCoordinatesQ D hdegree hs F P)) := by
  intro a z v i
  let e := IntrinsicPELMaps.pelRationalPeriodTateEquiv F.abelian P q
  let frame : Rational.rationalTateModule F.abelian.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q ≃ₗ[ℚ_[q]]
      Rational.SplitTateSpace s q :=
    D.splitPeriodFrame hg hdegree F.abelian P (periodCoordinatesQ D hdegree hs F P)
  let f := Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q)
    (End.endSchemeMap F.abelian.scheme (F.action a))
  change frame (f z) v i = _ * frame z v i
  obtain ⟨w, rfl⟩ := e.surjective z
  induction w using TensorProduct.inductionOn with
  | add w w' hw hw' =>
    simp only [e.map_add, f.map_add, frame.map_add, Pi.add_apply, hw, hw', mul_add]
  | tmul c w =>
    change D.splitPeriodFrame hg hdegree F.abelian P (periodCoordinatesQ D hdegree hs F P)
      (Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q)
        ((PELAdapters.actionFromEnd F.action).map a) (IntrinsicPELMaps.pelRationalPeriodTateEquiv F.abelian P q (c ⊗ₜ[ℚ] w))) v i = _
    rw [IntrinsicPELMaps.pelRationalPeriodTate_intertwines_apply, LinearMap.baseChange_tmul,
      splitPeriodFrame_period, splitPeriodFrame_period, periodCoordinatesQ_integer]
    change c * D.rationalLocalCharacter v
      ((a : E) * periodCoordinatesQ D hdegree hs F P w i) = _
    rw [map_mul, Data.SphericalPELAlbaneseData.rationalLocalCharacter_integer, PadicInt.algebraMap_apply]
    ring

include hg hdegree hs in
/-- A base equality transports a constructed frame and its proved action
compatibility together. The projective presentation is actual geometric data. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.exists_split_frame_of_complex_base {S : Scheme} (hS : S = Foundations.Scheme.ProjectiveSpace.complexBase)
    (G : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S)
    (Q : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation G.abelian.scheme) :
    ∃ e : Rational.SplitTateFrame s G.abelian.scheme (Over.mk (𝟙 S)) q,
      Rational.IsSplitActionFrame G (Over.mk (𝟙 S)) q D.localCharacter e := by
  subst S
  let P' := AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation Q
  exact ⟨D.splitPeriodFrame hg hdegree G.abelian P' (periodCoordinatesQ D hdegree hs G P'),
    splitPeriodFrame_action D hg hdegree hs G P'⟩

-- Keep the geometric interface's exact field-to-ring projection. A notation
-- expands before elaboration and avoids dependent comparison through a base alias.
local notation "fiberBase" => Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField))

private theorem complexGeometricBase_eq : fiberBase = Foundations.Scheme.ProjectiveSpace.complexBase := rfl

variable (h : D.HasIntegralModelGeometry)
  (b : fiberBase ⟶ Spec (.of K)) (x : D.GeometricPoint b)

include hg hdegree hs h in
private theorem complexSplitFrame_exists :
    ∃ e : D.FiberFrame b x,
      Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 fiberBase)) q D.localCharacter e :=
  D.exists_split_frame_of_complex_base hg hdegree hs (S := fiberBase)
    complexGeometricBase_eq (D.fiberFamily b x)
    (D.fiberProjectivePresentation h b x)

/-- A compatible frame constructed from the native periods of the actual fiber. -/
def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.complexSplitFrame : D.FiberFrame b x :=
  (complexSplitFrame_exists D hg hdegree hs h b x).choose

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.complexSplitFrame_equivariant :
    Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 fiberBase)) q D.localCharacter
      (D.complexSplitFrame hg hdegree hs h b x) :=
  (complexSplitFrame_exists D hg hdegree hs h b x).choose_spec

end AlgebraicGeometry.AbelianScheme.TateComparison.ComplexSplitEquivariance.SphericalPELAlbaneseData

end

end OAI
