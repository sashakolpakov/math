import OAI.AlgebraicGeometry.PELModuli.CMPoints.Generic
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFiber

/-! # Generic Moduli CM -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! CMAbelianVariety's arithmetic universal object has the same CM fibers as the
original fine PEL universal family, through the actual enhancement iso. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem GenericModuliCM.baseChangedFinePEL_nativeAt_hasCMH1_iff
    {E K L : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] [Field L] [NumberField L]
    {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (j : K →+* L)
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ (IntegralModel.PEL.ClassifyingBaseChange.baseChangedFinePELModel j M).space.left) :
    (IntrinsicFiber.nativePolarizedAt (IntegralModel.PEL.ClassifyingBaseChange.baseChangedFinePELModel j M).universal.polarized p).HasCMH1 ↔
    (IntrinsicFiber.nativePolarizedAt M.universal.polarized
      (p ≫ pullback.fst M.space.hom (Spec.map (CommRingCat.ofHom j)))).HasCMH1 :=
  IntrinsicFiber.nativePolarizedAt_pullback_hasCMH1_iff M.universal.polarized _ p

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

def Models.RankThreePELModel.genericModuliFinePoint (a : M.Family)
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ (M.embeddedReducedGenericModuli a).left) :
    Foundations.Scheme.ProjectiveSpace.complexBase ⟶ (M.moduli a).space.left :=
  ((p ≫ (M.embeddedGenericInclusion a).left) ≫
    pullback.fst (M.genericFinePEL a).space.hom
      (Spec.map (CommRingCat.ofHom M.arithmetic.embedding.rangeRestrictField))) ≫
    pullback.fst (M.moduli a).space.hom M.arithmetic.fieldExtension

theorem Models.RankThreePELModel.genericStandardModuli_hasCMH1_iff (hM : M.HasPrescribedBallPeriods) (a : M.Family)
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ (M.embeddedReducedGenericModuli a).left) :
    ((M.genericStandardModuli hM a).abelianAt p).HasCMH1 ↔
    (IntrinsicFiber.nativePolarizedAt (M.moduli a).universal.polarized (M.genericModuliFinePoint a p)).HasCMH1 := by
  obtain ⟨e⟩ := Submoduli.pelArithmeticSubmoduli_universalIso
    (Module.finBasis ℤ (NumberField.RingOfIntegers E))
    M.arithmetic.embedding.fieldRange (M.embeddedGenericFinePEL a)
    (hM.2.2 a).1 (hM.2.2 a).2.2.1.1
    (Fine.embeddedFinePEL_isFine M.arithmetic.embedding (M.genericFinePEL a) (M.genericFinePEL_isFine hM a))
    (M.embeddedGenericInclusion a) (by
      let : IsProper (M.embeddedReducedGenericModuli a).hom := M.embeddedReducedGenericModuli_proper hM a
      infer_instance)
  have h := IntrinsicFiber.nativePolarizedAt_iso_hasCMH1_iff
    (P := (M.genericArithmeticModuli hM a).universal.polarized)
    (Q := (M.embeddedGenericFinePEL a).universal.polarized.pullback
      (M.embeddedGenericInclusion a).left) e.polarized.abelian p
  exact h.trans ((IntrinsicFiber.nativePolarizedAt_pullback_hasCMH1_iff
    (M.embeddedGenericFinePEL a).universal.polarized (M.embeddedGenericInclusion a).left p).trans
      ((GenericModuliCM.baseChangedFinePEL_nativeAt_hasCMH1_iff
    (M.genericFinePEL a) M.arithmetic.embedding.rangeRestrictField _).trans
      (GenericModuliCM.baseChangedFinePEL_nativeAt_hasCMH1_iff (M.moduli a)
        (algebraMap K M.arithmetic.extension.carrier) _)))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
