import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FinePELPointClassification
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PELObject
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FixedBasis

/-! # Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The reference lattice fibers give actual points of the constructed
native complex moduli scheme, with exact polarized family recovery. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (he : κ.comp iota = P.μ)

def Models.FinePELModel.referencePoint (z : P.domain) : M.ComplexPoints κ :=
  (M.complexPointClassEquiv κ hM).symm (P.referencePELObject hP z iota κ he N).classOf

theorem Models.FinePELModel.referencePoint_class (z : P.domain) :
    (M.universal.pullback (M.complexPointBaseEquiv κ (M.referencePoint hM κ hP he z))).classOf =
      (P.referencePELObject hP z iota κ he N).classOf :=
  (M.complexPointClassEquiv κ hM).apply_symm_apply _

theorem Models.FinePELModel.referencePoint_recovery (z : P.domain) : Nonempty
    (Models.PELPullbackIso M.universal (P.referencePELObject hP z iota κ he N)
      (M.complexPointBaseEquiv κ (M.referencePoint hM κ hP he z))) :=
  (Models.PELPullbackIso.nonempty_iff_classOf _).mpr (M.referencePoint_class hM κ hP he z).symm

theorem Models.FinePELModel.referencePoint_eq_iff (z w : P.domain) :
    M.referencePoint hM κ hP he z = M.referencePoint hM κ hP he w ↔
      Nonempty (PEL.Objects.PELIso (P.referencePELObject hP z iota κ he N) (P.referencePELObject hP w iota κ he N)) :=
  (M.complexPointClassEquiv κ hM).symm.injective.eq_iff.trans (PEL.Objects.PELObject.classOf_eq_iff _ _)

include hM hP he in
theorem Models.FinePELModel.complexPoints_nonempty_of_admissible : Nonempty (M.ComplexPoints κ) :=
  ⟨M.referencePoint hM κ hP he (P.referenceOrigin hP)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
