import OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD
import OAI.NumberTheory.PadicHodge.GeometricComparison.FrobeniusDifferential

/-! # One Forms -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.OneForms.IntegralOneForms

noncomputable section

/-! In degree one, the original differential-symbol presentation equals Kähler differentials over any coefficient ring, before inverting the prime. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

def toOne : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 1 →ₗ[A] KaehlerDifferential R A :=
  (exteriorPower.oneEquiv A (KaehlerDifferential R A)).toLinearMap.comp (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R A 1)

def fromOne : KaehlerDifferential R A →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 1 :=
  (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols R A 1).toLinearMap (fun _ => 0) 0

theorem toOne_symbol (a : A) (v : Fin 1 → A) :
    toOne R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = a • KaehlerDifferential.D R A (v 0) := by
  rw [toOne, LinearMap.comp_apply, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol, map_smul]
  exact congrArg (fun x => a • x)
    (exteriorPower.oneEquiv_ιMulti (fun i => KaehlerDifferential.D R A (v i)))

theorem fromOne_D (a : A) : fromOne R A (KaehlerDifferential.D R A a) =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 (fun _ => a) := by
  change AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols R A 1
    (Function.update (fun _ => 0) 0 (KaehlerDifferential.D R A a)) = _
  rw [show Function.update (fun _ : Fin 1 => (0 : KaehlerDifferential R A)) 0
    (KaehlerDifferential.D R A a) = (fun _ => KaehlerDifferential.D R A a) by
      funext i; have hi : i = 0 := Subsingleton.elim _ _; subst i; simp]
  exact AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols_D R A 1 (fun _ => a)

theorem left_inverse : Function.LeftInverse (fromOne R A) (toOne R A) := by
  intro ω
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A 1) ω
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single v a =>
    change fromOne R A (toOne R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v
    rw [toOne_symbol, map_smul, fromOne_D, ← AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one]
    congr 1
    funext i
    exact congrArg v (Subsingleton.elim _ _)

def equiv : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 1 ≃ₗ[A] KaehlerDifferential R A :=
  LinearEquiv.ofBijective (toOne R A) ⟨(left_inverse R A).injective,
    (exteriorPower.oneEquiv A (KaehlerDifferential R A)).surjective.comp (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_surjective R A 1)⟩

variable {R A}

theorem naturality {B C : CommAlgCat.{u} R} (f : B ⟶ C) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B 1) :
    equiv R C (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f 1 ω) = AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsMap f (equiv R B ω) := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R B 1) ω
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single v a =>
    change toOne R C (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f 1 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B a v)) =
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsMap f (toOne R B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B a v))
    rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, toOne_symbol, toOne_symbol,
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsMap_smul, AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsMap_D]

theorem frobenius_divisible (p : ℕ) (B : CommAlgCat.{u} R) (f : B ⟶ B)
    (h : ∀ a : B, ∃ b : B, f a = a ^ p + (p : B) * b) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B 1) :
    ∃ η : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B 1, AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f 1 ω = p • η := by
  obtain ⟨η, hη⟩ := FrobeniusDifferential.FrobeniusDifferentialDivisibility.on_oneForms p B f h (equiv R B ω)
  refine ⟨(equiv R B).symm η, (equiv R B).injective ?_⟩
  rw [naturality, map_nsmul, LinearEquiv.apply_symm_apply]
  exact hη

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.OneForms.IntegralOneForms
