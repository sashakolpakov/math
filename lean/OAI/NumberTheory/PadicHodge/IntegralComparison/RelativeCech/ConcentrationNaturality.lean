import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Concentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConcentrationNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentrationLocalRecovery
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechTotalCoordinates

/-! # Concentration Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ConcentrationNaturality

noncomputable section

/-! Relative extension and forward refinements commute with the original
concentration arrows. The source complex is never inverted along a cover refinement. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CoefficientQuasiIso
variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i))

abbrev cover := Intersections.cover U V

include hU hV in
omit [X.IsSeparated] [LinearOrder ι] in
theorem cover_affine (i : WithBot ι) : IsAffineOpen (cover U V i) := by
  cases i with
  | bot => exact hU
  | coe i => exact hV i

abbrev globalFunctor (q : ℕ) :=
  Cech.ConcentrationNaturality.totalFunctor π (cover U V) ⋙
    homologyFunctor (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) q

variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

abbrev globalIso (q : ℕ) := Cech.CohomologyConcentration.homologyIso π (cover U V)
  (cover_affine U hU V hV) K c hK q

abbrev extension (L : CochainComplex X.Modules ℕ) (q : ℕ) :=
  homologyMap (Total.map U V (CoefficientQuasiIso.coefficients π L)) q ≫
    (homologyMapIso (IntrinsicOrdered.CechTotalCoordinates.Intrinsic.iso π (cover U V) L) q).hom

omit [X.IsSeparated] in
theorem extension_naturality {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) (q : ℕ) :
    (Concentration.functor π U V q).map a ≫ extension π U V L q =
      extension π U V K q ≫ (globalFunctor π U V q).map a :=
  DualComplexHomology.compose_squares _ _ _ _ _ _ _
    (Total.homology_naturality U V (CoefficientQuasiIso.coefficientMap π a) q)
    (IntrinsicOrdered.CechTotalCoordinates.Intrinsic.homology_naturality π (cover U V) a q)

@[reassoc]
theorem extension_square (q : ℕ) :
    (Concentration.iso π U hU V hV K c hK q).hom ≫
      extension π U V ((single X.Modules (.up ℕ) c).obj (K.homology c)) q =
        extension π U V K q ≫ (globalIso π U hU V hV K c hK q).hom := by
  let := Concentration.projection_isIso π U hU V hV K c hK q
  let := Concentration.inclusion_isIso π U hU V hV K c hK q
  let := Cech.ConcentrationNaturality.projection_quasiIso π (cover U V)
    (cover_affine U hU V hV) K c hK
  let := Cech.ConcentrationNaturality.inclusion_quasiIso π (cover U V)
    (cover_affine U hU V hV) K c hK
  let : IsIso ((globalFunctor π U V q).map (CohomologyConcentration.projection K c)) := by
    change IsIso (homologyMap
      ((Cech.ConcentrationNaturality.totalFunctor π (cover U V)).map (CohomologyConcentration.projection K c)) q)
    infer_instance
  let : IsIso ((globalFunctor π U V q).map (CohomologyConcentration.inclusion K c)) := by
    change IsIso (homologyMap
      ((Cech.ConcentrationNaturality.totalFunctor π (cover U V)).map (CohomologyConcentration.inclusion K c)) q)
    infer_instance
  exact ConcentrationLocalRecovery.square (Concentration.functor π U V q) (globalFunctor π U V q) K c
    (extension π U V K q) (extension π U V (CohomologyConcentration.truncation K c) q)
    (extension π U V ((single X.Modules (.up ℕ) c).obj (K.homology c)) q)
    (extension_naturality π U V (CohomologyConcentration.projection K c) q)
    (extension_naturality π U V (CohomologyConcentration.inclusion K c) q)

variable (W : κ → X.Opens) (hW : ∀ i, IsAffineOpen (W i))
  (r : FormalCoproduct.mk κ W ⟶ FormalCoproduct.mk ι V)

@[reassoc]
theorem refinement_square (q : ℕ) :
    (Concentration.iso π U hU V hV K c hK q).hom ≫
      Refinement.homology U V W r
        (CoefficientQuasiIso.coefficients π ((single X.Modules (.up ℕ) c).obj (K.homology c))) q =
    Refinement.homology U V W r (CoefficientQuasiIso.coefficients π K) q ≫
      (Concentration.iso π U hU W hW K c hK q).hom := by
  let := Concentration.projection_isIso π U hU V hV K c hK q
  let := Concentration.inclusion_isIso π U hU V hV K c hK q
  let := Concentration.projection_isIso π U hU W hW K c hK q
  let := Concentration.inclusion_isIso π U hU W hW K c hK q
  exact ConcentrationLocalRecovery.square (Concentration.functor π U V q) (Concentration.functor π U W q) K c
    (Refinement.homology U V W r (CoefficientQuasiIso.coefficients π K) q)
    (Refinement.homology U V W r (CoefficientQuasiIso.coefficients π (CohomologyConcentration.truncation K c)) q)
    (Refinement.homology U V W r
      (CoefficientQuasiIso.coefficients π ((single X.Modules (.up ℕ) c).obj (K.homology c))) q)
    (Refinement.homology_naturality U V W r (CoefficientQuasiIso.coefficientMap π (CohomologyConcentration.projection K c)) q)
    (Refinement.homology_naturality U V W r (CoefficientQuasiIso.coefficientMap π (CohomologyConcentration.inclusion K c)) q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ConcentrationNaturality
