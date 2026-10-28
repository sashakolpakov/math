import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.FrameFactorization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.GeometricLevel
import Mathlib.Algebra.CharZero.AddMonoidHom

/-! # Characteristic Zero Level Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.CharacteristicZeroLevelCover.IntegralLevelCover

noncomputable section

/-! In characteristic zero the integral full-frame parameter is
surjective at every nonzero level, over arbitrary bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {g L N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    {K : Type} [Field K] [CharZero K] (b : S ⟶ Spec (.of K)) [NeZero L]
    (hL : ∀ x : S, IsUnit (L : S.presheaf.stalk x))

include b in
theorem characteristicZero_fullFrame_surjective :
    Surjective (FrameLocus.IntegralLevelCover.fullFrameScheme A.abelian hL).hom := by
  constructor
  intro x
  let k := AlgebraicClosure (S.residueField x)
  let q : Spec (.of k) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) k)) ≫ S.fromSpecResidueField x
  let constants : K →+* k := (Spec.preimage (q ≫ b)).hom
  let : CharZero k := CharZero.of_addMonoidHom constants.toAddMonoidHom
    constants.map_one constants.injective
  let β := AbelianModuli.ReferenceFamily.Geometric.GeometricLevel.geometricPolarizedFullLevel (A.pullback q) L
  let f := FrameFactorization.IntegralLevelCover.fullFrameOfRelativeLevel A.abelian hL (Over.mk q) β
  refine ⟨f.left (default : Spec (.of k)), ?_⟩
  exact (congrArg (fun a : Spec (.of k) ⟶ S => a default) f.w).trans
    (S.fromSpecResidueField_apply x _)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.CharacteristicZeroLevelCover.IntegralLevelCover
