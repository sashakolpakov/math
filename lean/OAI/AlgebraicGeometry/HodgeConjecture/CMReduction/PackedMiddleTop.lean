import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.MiddleTop
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedRegroup
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.AmplePowers

/-! # Packed Middle Top -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedMiddleTop.CM.Construction

noncomputable section

/-! The nonzero middle top classes are exactly the cup of the selected
H1 pair and the geometric ample power, in both required orientations. -/

open _root_.CategoryTheory

def packAmple (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace V.toOver) :=
  PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace V.toOver) k
    (V.rationalCohomologyInclusion (k + k) (ComplexMultiplication.HodgeComparison.Powers.CM.Construction.fubiniStudyPowerQ V k))

theorem packAmple_algebraic (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) : PackedRegroup.CM.Construction.IsAlgebraicEven V (packAmple V k) :=
  AmplePowers.CM.Construction.complex_amplePower_algebraic hlefschetz h_LineBundleCycles h_ThomClass V k

def topCupClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k d : ℕ) (hd : 1 + k = d)
    (u v : V.complexCohomology 1) : V.complexCohomology (d + d) :=
  AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace V.toOver)) (ModuleCat.of ℂ ℂ)
    (by omega : 2 + (k + k) = d + d) (ComplexMultiplication.HodgeComparison.TopCup.CM.Construction.complexH1TopCup V k u v)

theorem pack_topCupClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k d : ℕ) (hd : 1 + k = d)
    (u v : V.complexCohomology 1) :
    PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace V.toOver) d (topCupClass V k d hd u v) =
      PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace V.toOver) u v * packAmple V k := by
  change (⟨d, topCupClass V k d hd u v⟩ : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace V.toOver)) =
    ⟨1 + k, ComplexOperations.CM.Construction.evenCup ℂ (Betti.Scheme.schemePointSpace V.toOver) 1 k
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace V.toOver) 1 1 u v)
      (V.rationalCohomologyInclusion (k + k) (ComplexMultiplication.HodgeComparison.Powers.CM.Construction.fubiniStudyPowerQ V k))⟩
  apply Sigma.ext hd.symm
  exact (EvenAlgebra.CM.Construction.cohomologyCast_heq (R := ℂ) (Betti.Scheme.schemePointSpace V.toOver)
    (show 2 + (k + k) = d + d by omega) (ComplexMultiplication.HodgeComparison.TopCup.CM.Construction.complexH1TopCup V k u v)).trans
      (EvenAlgebra.CM.Construction.evenCup_heq_cup (R := ℂ) (Betti.Scheme.schemePointSpace V.toOver) 1 k _ _).symm

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

theorem pack_middleTopClass (v : Pairing.CM.Construction.SignType E)
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v)) :
    PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace R.abelianVariety.toOver) R.abelianVariety.variety.complexDimension
      (MiddleTop.CM.Construction.middleTopClass E v R) =
      PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace R.abelianVariety.toOver)
        (Endpoints.CM.Construction.realizedVector E R (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) (Endpoints.CM.Construction.realizedVector E R 1) *
      packAmple R.abelianVariety.variety (R.abelianVariety.variety.complexDimension - 1) :=
  pack_topCupClass R.abelianVariety.variety _ _
    (by have := MiddleTop.CM.Construction.realization_dimension_pos E R; omega) _ _

def reverseMiddleTopClass (v : Pairing.CM.Construction.SignType E)
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v)) :
    R.abelianVariety.variety.complexCohomology
      (R.abelianVariety.variety.complexDimension + R.abelianVariety.variety.complexDimension) :=
  topCupClass R.abelianVariety.variety (R.abelianVariety.variety.complexDimension - 1)
    R.abelianVariety.variety.complexDimension (by have := MiddleTop.CM.Construction.realization_dimension_pos E R; omega)
    (Endpoints.CM.Construction.realizedVector E R 1) (Endpoints.CM.Construction.realizedVector E R (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))

theorem reverseMiddleTopClass_eq_neg (v : Pairing.CM.Construction.SignType E)
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v)) :
    reverseMiddleTopClass E v R = -MiddleTop.CM.Construction.middleTopClass E v R := by
  have hpair := CupRegrouping.CM.SurfaceConstruction.cup11_anticomm (R := ℂ) (Betti.Scheme.schemePointSpace R.abelianVariety.toOver)
    (Endpoints.CM.Construction.realizedVector E R 1) (Endpoints.CM.Construction.realizedVector E R (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))
  unfold reverseMiddleTopClass topCupClass MiddleTop.CM.Construction.middleTopClass ComplexMultiplication.HodgeComparison.TopCup.CM.Construction.complexH1TopCup
  simp only [LinearMap.compr₂_apply, hpair, map_neg]

theorem reverseMiddleTopClass_ne_zero (h_PolarizedPairing : Pairing.CM.Construction.PolarizedPairingInput) (v : Pairing.CM.Construction.SignType E)
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v)) :
    reverseMiddleTopClass E v R ≠ 0 := by
  rw [reverseMiddleTopClass_eq_neg]
  exact neg_ne_zero.mpr (MiddleTop.CM.Construction.middleTopClass_ne_zero E h_PolarizedPairing v R)

theorem pack_reverseMiddleTopClass (v : Pairing.CM.Construction.SignType E)
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v)) :
    PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace R.abelianVariety.toOver) R.abelianVariety.variety.complexDimension
      (reverseMiddleTopClass E v R) =
      PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace R.abelianVariety.toOver)
        (Endpoints.CM.Construction.realizedVector E R 1) (Endpoints.CM.Construction.realizedVector E R (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) *
      packAmple R.abelianVariety.variety (R.abelianVariety.variety.complexDimension - 1) :=
  pack_topCupClass R.abelianVariety.variety _ _
    (by have := MiddleTop.CM.Construction.realization_dimension_pos E R; omega) _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedMiddleTop.CM.Construction
