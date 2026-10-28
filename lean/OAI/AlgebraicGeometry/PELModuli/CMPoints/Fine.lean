import OAI.AlgebraicGeometry.PELModuli.CMPoints.Enhancement
import OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.ClassifyingBaseChange

/-! # Fine -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Fine

noncomputable section

/-! The actual fine PEL model, with a finite integral basis of its action,
is an arithmetic moduli space of precisely the kind used by CMAbelianVariety. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]
  (K : Subfield ℂ) [NumberField K]
  {s N r : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}

def pelArithmeticModuli
    (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E))
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hP : P.IsAdmissible)
    (hN : 3 ≤ N) (hM : M.IsFine) (hfinite : LocallyOfFiniteType M.space.hom) :
    ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ArithmeticAbelianModuli := {
    dimension := 3 * s
    polarizationType := P.polarizationType
    polarizationType_pos := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpos, _⟩ := hP
      exact hpos
    polarizationType_chain := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hchain, _⟩ := hP
      exact hchain
    level := N
    deepLevel := hN
    endomorphismCount := r
    baseField := K
    numberField := inferInstance
    parameter := M.space
    locallyFiniteType := hfinite
    locus := Enhancement.pelEnhancementLocus b
    represents := Enhancement.pelEnhancementRepresentable b M hM }

theorem pelArithmeticModuli_universalClass
    (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E))
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hP : P.IsAdmissible)
    (hN : 3 ≤ N) (hM : M.IsFine) (hfinite : LocallyOfFiniteType M.space.hom) :
    (pelArithmeticModuli K b M hP hN hM hfinite).universalClass =
      (Enhancement.pelEnhancement b M.universal).classOf := by
  change Enhancement.pelEnhancementClasses b
    (AbelianModuli.ReferenceFamily.PEL.Objects.PELClasses.pullback (𝟙 M.space) M.universal.classOf) = _
  rw [AbelianModuli.ReferenceFamily.PEL.Objects.PELClasses.pullback_id]
  rfl

theorem pelArithmeticModuli_universalIso
    (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E))
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hP : P.IsAdmissible)
    (hN : 3 ≤ N) (hM : M.IsFine) (hfinite : LocallyOfFiniteType M.space.hom) :
    Nonempty (ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianIso
      (pelArithmeticModuli K b M hP hN hM hfinite).universal
      (Enhancement.pelEnhancement b M.universal)) := by
  apply (ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianData.classOf_eq_iff _ _).mp
  exact (ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ArithmeticAbelianModuli.universal_classOf _).trans
    (pelArithmeticModuli_universalClass K b M hP hN hM hfinite)

variable {K' : Type} [Field K'] [NumberField K'] (κ : K' →+* ℂ)

instance numberField_complexRange : NumberField κ.fieldRange :=
  NumberField.of_ringEquiv K' κ.fieldRange κ.rangeRestrictFieldEquiv

/-- Replace an abstract coefficient field by its actual image in C,
using the canonical base change of the same fine PEL family. -/
def embeddedFinePEL {iota' : E →+* K'}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota' N) :
    AbelianModuli.ReferenceFamily.Models.FinePELModel P (κ.rangeRestrictField.comp iota') N :=
  IntegralModel.PEL.ClassifyingBaseChange.baseChangedFinePELModel κ.rangeRestrictField M

theorem embeddedFinePEL_isFine {iota' : E →+* K'}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota' N) (hM : M.IsFine) :
    (embeddedFinePEL κ M).IsFine :=
  IntegralModel.PEL.ClassifyingBaseChange.finePEL_isFine_baseChange κ.rangeRestrictField M hM

/-- The CMAbelianVariety arithmetic interface for an abstract number-field PEL model,
with no new representability hypothesis. -/
def embeddedArithmeticModuli {iota' : E →+* K'}
    (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E))
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota' N) (hP : P.IsAdmissible)
    (hN : 3 ≤ N) (hM : M.IsFine) (hfinite : LocallyOfFiniteType M.space.hom) :
    ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ArithmeticAbelianModuli :=
  pelArithmeticModuli κ.fieldRange b (embeddedFinePEL κ M) hP hN
    (embeddedFinePEL_isFine κ M hM) (by
      let : LocallyOfFiniteType M.space.hom := hfinite
      exact inferInstanceAs (LocallyOfFiniteType
        (CategoryTheory.Limits.pullback.snd M.space.hom
          (Spec.map (CommRingCat.ofHom κ.rangeRestrictField)))))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Fine
