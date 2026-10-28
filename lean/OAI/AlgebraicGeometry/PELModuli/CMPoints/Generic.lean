import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Submoduli
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Standard
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization

/-! # Generic -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The reduced generic model supplied by IntegralModel is an actual finite-type
enhanced moduli space for CMAbelianVariety. Its finite type property comes from the
given proper integral model, not from an additional fine-model hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

abbrev Models.RankThreePELModel.genericFinePEL (a : M.Family) :=
  IntegralModel.PEL.ClassifyingBaseChange.baseChangedFinePELModel (algebraMap K M.arithmetic.extension.carrier) (M.moduli a)

theorem Models.RankThreePELModel.genericFinePEL_isFine (hM : M.HasPrescribedBallPeriods) (a : M.Family) :
    (M.genericFinePEL a).IsFine := by
  obtain ⟨_, _, _, hFine, _⟩ := hM.2.2 a
  exact IntegralModel.PEL.ClassifyingBaseChange.finePEL_isFine_baseChange _ (M.moduli a) hFine

abbrev Models.RankThreePELModel.reducedGenericModuli (a : M.Family) :=
  (Over.pullback M.arithmetic.fieldExtension).obj (IntegralModel.Reduction.reduction (M.moduli a).space)

def Models.RankThreePELModel.reducedGenericInclusion (a : M.Family) : M.reducedGenericModuli a ⟶ (M.genericFinePEL a).space :=
  (Over.pullback M.arithmetic.fieldExtension).map (IntegralModel.Reduction.reductionι (M.moduli a).space)

instance Models.RankThreePELModel.reducedGenericInclusion_closed (a : M.Family) :
    IsClosedImmersion (M.reducedGenericInclusion a).left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (IntegralModel.Specialization.base_change_square M.arithmetic.fieldExtension (IntegralModel.Reduction.reductionι (M.moduli a).space))
    inferInstance

instance Models.RankThreePELModel.reducedGenericInclusion_mono (a : M.Family) : Mono (M.reducedGenericInclusion a) :=
  Over.mono_of_mono_left _

theorem Models.RankThreePELModel.reducedGenericModuli_proper (hM : M.HasPrescribedBallPeriods) (a : M.Family) :
    IsProper (M.reducedGenericModuli a).hom := by
  obtain ⟨_, _, _, _, _, _, _, hp, _⟩ := hM.2.2 a
  let : IsProper (M.integral a).toOver.hom := hp
  let e := (M.integral a).genericIso
  have : IsIso e.inv.left := inferInstanceAs
    (IsIso (((Over.forget (IntegralModel.Arithmetic.Open.fieldBase M.arithmetic.extension.carrier)).mapIso e).inv))
  have : IsProper ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver).hom :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd
      (M.integral a).toOver.hom M.arithmetic.generic))
  rw [← e.inv.w]
  infer_instance

abbrev Models.RankThreePELModel.embeddedGenericFinePEL (a : M.Family) := Fine.embeddedFinePEL M.arithmetic.embedding (M.genericFinePEL a)

abbrev Models.RankThreePELModel.embeddedReducedGenericModuli (a : M.Family) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom M.arithmetic.embedding.rangeRestrictField))).obj
    (M.reducedGenericModuli a)

def Models.RankThreePELModel.embeddedGenericInclusion (a : M.Family) :
    M.embeddedReducedGenericModuli a ⟶ (M.embeddedGenericFinePEL a).space :=
  (Over.pullback (Spec.map (CommRingCat.ofHom M.arithmetic.embedding.rangeRestrictField))).map
    (M.reducedGenericInclusion a)

instance Models.RankThreePELModel.embeddedGenericInclusion_closed (a : M.Family) :
    IsClosedImmersion (M.embeddedGenericInclusion a).left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (IntegralModel.Specialization.base_change_square (Spec.map (CommRingCat.ofHom M.arithmetic.embedding.rangeRestrictField))
      (M.reducedGenericInclusion a)) inferInstance

instance Models.RankThreePELModel.embeddedGenericInclusion_mono (a : M.Family) : Mono (M.embeddedGenericInclusion a) :=
  Over.mono_of_mono_left _

theorem Models.RankThreePELModel.embeddedReducedGenericModuli_proper (hM : M.HasPrescribedBallPeriods) (a : M.Family) :
    IsProper (M.embeddedReducedGenericModuli a).hom := by
  let : IsProper (M.reducedGenericModuli a).hom := M.reducedGenericModuli_proper hM a
  exact inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd
    (M.reducedGenericModuli a).hom
    (Spec.map (CommRingCat.ofHom M.arithmetic.embedding.rangeRestrictField))))

def Models.RankThreePELModel.genericArithmeticModuli (hM : M.HasPrescribedBallPeriods) (a : M.Family) :
    ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ArithmeticAbelianModuli :=
  Submoduli.pelArithmeticSubmoduli (Module.finBasis ℤ (NumberField.RingOfIntegers E))
    M.arithmetic.embedding.fieldRange (M.embeddedGenericFinePEL a)
    (hM.2.2 a).1 (hM.2.2 a).2.2.1.1
    (Fine.embeddedFinePEL_isFine M.arithmetic.embedding (M.genericFinePEL a) (M.genericFinePEL_isFine hM a))
    (M.embeddedGenericInclusion a) (by
      let : IsProper (M.embeddedReducedGenericModuli a).hom := M.embeddedReducedGenericModuli_proper hM a
      infer_instance)

def Models.RankThreePELModel.genericStandardModuli (hM : M.HasPrescribedBallPeriods) (a : M.Family) :
    ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.StandardAbelianModuli := Standard.standardModuliOfArithmetic (M.genericArithmeticModuli hM a)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
