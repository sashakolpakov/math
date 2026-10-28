import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionMapBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.Purity

/-! # Coefficient Evaluation Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientEvaluationBaseChange

noncomputable section

/-! Quotient coefficient evaluation commutes with flat base change.
The coefficient hypotheses are literal tensor squares; the purity
normalization enters only for the scalar quotient. -/

open _root_.CategoryTheory
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation OAI.NumberTheory.PadicHodge.IntegralComparison.DualBaseChangeNaturality

variable (R S Q Q' : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [Module.Flat R S] [CommRing Q] [CommRing Q'] [Algebra R Q] [Algebra S Q']
  (C C' : Type u) [AddCommGroup C] [AddCommGroup C']
  [Module Q C] [Module R C] [IsScalarTower R Q C]
  [Module Q' C'] [Module S C'] [IsScalarTower S Q' C']
  (q : (DualBaseChangeNaturality.tensorFunctor R S).obj (ModuleCat.of R Q) ⟶ ModuleCat.of S Q')
  (t : (DualBaseChangeNaturality.tensorFunctor R S).obj (ModuleCat.of R C) ⟶ ModuleCat.of S C')
  (α : Q → Q') (β : C → C')
  (hq : ∀ (a : S) (x : Q), q (a ⊗ₜ[R] x) = a • α x)
  (ht : ∀ (a : S) (x : C), t (a ⊗ₜ[R] x) = a • β x)
  (hβ : ∀ (x : Q) (m : C), β (x • m) = α x • β m)

include hq ht hβ in
omit [Module.Flat R S] in
theorem point_square (m : C) :
    (DualBaseChangeNaturality.tensorFunctor R S).map (Quotient.CoefficientEvaluation.point R Q C m) ≫ t =
      q ≫ Quotient.CoefficientEvaluation.point S Q' C' (β m) := by
  apply ConcreteCategory.hom_ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
      change t (a ⊗ₜ[R] (x • m)) = (q (a ⊗ₜ[R] x)) • β m
      rw [ht, hq, hβ, smul_assoc]
  | add x y hx hy => simpa only [_root_.map_add] using congrArg₂ (· + ·) hx hy

variable (P : ProjectiveResolution (ModuleCat.of R Q))
  (PC : ProjectiveResolution (ModuleCat.of R C))
  (P' : ProjectiveResolution (ModuleCat.of S Q'))
  (PC' : ProjectiveResolution (ModuleCat.of S C'))
  [∀ i, Module.Free R (P.complex.X i)] [∀ i, Module.Finite R (P.complex.X i)]
  [∀ i, Module.Free R (PC.complex.X i)] [∀ i, Module.Finite R (PC.complex.X i)]
  (eP : (DualBaseChangeNaturality.tensorComplex R S).obj P.complex ≅ P'.complex)
  (ePC : (DualBaseChangeNaturality.tensorComplex R S).obj PC.complex ≅ PC'.complex)
  (hP : eP.hom.f 0 ≫ P'.π.f 0 = (DualBaseChangeNaturality.tensorFunctor R S).map (P.π.f 0) ≫ q)
  (hPC : ePC.hom.f 0 ≫ PC'.π.f 0 = (DualBaseChangeNaturality.tensorFunctor R S).map (PC.π.f 0) ≫ t)
  (T : ModuleCat.{u} R) (T' : ModuleCat.{u} S)
  (eT : T ≅ ModuleCat.of R R) (eT' : T' ≅ ModuleCat.of S S)
  (n : ℕ)

include hq ht hβ hP hPC in
theorem pullback (x : Quotient.CoefficientEvaluation.group R T n PC) (m : C) :
    Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor S T') P' PC' (Quotient.CoefficientEvaluation.point S Q' C' (β m)) n
        ((LinearHomBaseChange.homologyIso R S PC.complex PC'.complex ePC T T' eT eT' n).hom
          (1 ⊗ₜ[R] x)) =
      (LinearHomBaseChange.homologyIso R S P.complex P'.complex eP T T' eT eT' n).hom
        (1 ⊗ₜ[R] Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PC (Quotient.CoefficientEvaluation.point R Q C m) n x) := by
  have h := ResolutionMapBaseChange.Linear.naturality R S P PC P' PC' eP ePC q t hP hPC
    (Quotient.CoefficientEvaluation.point R Q C m) (Quotient.CoefficientEvaluation.point S Q' C' (β m))
    (point_square R S Q Q' C C' q t α β hq ht hβ m) T T' eT eT' n
  have hx := ConcreteCategory.congr_hom h (1 ⊗ₜ[R] x)
  change (LinearHomBaseChange.homologyIso R S P.complex P'.complex eP T T' eT eT' n).hom
      (1 ⊗ₜ[R] Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PC (Quotient.CoefficientEvaluation.point R Q C m) n x) = _ at hx
  exact hx.symm

variable (L L' : Type u) [AddCommGroup L] [AddCommGroup L']
  [Module Q L] [Module R L] [IsScalarTower R Q L]
  [Module Q' L'] [Module S L'] [IsScalarTower S Q' L']
  (eL : Quotient.CoefficientEvaluation.group R T n P ≅ ModuleCat.of R L)
  (eL' : Quotient.CoefficientEvaluation.group S T' n P' ≅ ModuleCat.of S L')
  (ell : L → L')
  (hL : ∀ x : Quotient.CoefficientEvaluation.group R T n P,
    eL'.hom ((LinearHomBaseChange.homologyIso R S P.complex P'.complex eP T T' eT eT' n).hom
      (1 ⊗ₜ[R] x)) = ell (eL.hom x))
  [Module.Finite Q C] [Module.Projective Q C]
  [Module.Finite Q' C'] [Module.Projective Q' C']
  (hQ : Function.Surjective (algebraMap R Q))
  (hQ' : Function.Surjective (algebraMap S Q'))
  (e : Quotient.CoefficientEvaluation.group R T n P ≅ ModuleCat.of R Q)
  (e' : Quotient.CoefficientEvaluation.group S T' n P' ≅ ModuleCat.of S Q')

include hq ht hβ hP hPC hL in
theorem evaluation (x : Quotient.CoefficientEvaluation.group R T n PC) (m : C) :
    ProjectiveCoefficient.Purity.equiv S Q' hQ' T' n P' e' C' PC' L' eL'
        ((LinearHomBaseChange.homologyIso R S PC.complex PC'.complex ePC T T' eT eT' n).hom
          (1 ⊗ₜ[R] x)) (β m) =
      ell (ProjectiveCoefficient.Purity.equiv R Q hQ T n P e C PC L eL x m) := by
  rw [ProjectiveCoefficient.Purity.equiv_apply, ProjectiveCoefficient.Purity.equiv_apply,
    pullback R S Q Q' C C' q t α β hq ht hβ P PC P' PC' eP ePC hP hPC T T' eT eT' n]
  exact hL _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientEvaluationBaseChange
