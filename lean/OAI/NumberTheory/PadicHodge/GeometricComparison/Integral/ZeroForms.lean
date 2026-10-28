import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.OneForms

/-! # Zero Forms -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ZeroForms.IntegralZeroForms

noncomputable section

/-! The original degree-zero forms are the coordinate ring over arbitrary coefficients, with the actual first differential and pullback. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

def toZero : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 0 →ₗ[A] A :=
  (exteriorPower.zeroEquiv A (KaehlerDifferential R A)).toLinearMap.comp (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R A 0)

def fromZero : A →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 0 :=
  LinearMap.toSpanSingleton A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 0) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 (fun i => Fin.elim0 i))

theorem toZero_symbol (a : A) (v : Fin 0 → A) : toZero R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = a := by
  rw [toZero, LinearMap.comp_apply, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol, map_smul]
  change a • exteriorPower.zeroEquiv A (KaehlerDifferential R A)
    (exteriorPower.ιMulti A 0 (fun i => KaehlerDifferential.D R A (v i))) = a
  rw [exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]

theorem fromZero_apply (a : A) :
    fromZero R A a = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (fun i => Fin.elim0 i) :=
  (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one R A a (fun i => Fin.elim0 i)).symm

theorem left_inverse : Function.LeftInverse (fromZero R A) (toZero R A) := by
  intro ω
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A 0) ω
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single v a =>
    change fromZero R A (toZero R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v
    rw [toZero_symbol, fromZero_apply]
    congr 1
    exact funext (fun i => Fin.elim0 i)

def equiv : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 0 ≃ₗ[A] A :=
  LinearEquiv.ofBijective (toZero R A) ⟨(left_inverse R A).injective,
    fun a => ⟨AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (fun i => Fin.elim0 i), toZero_symbol R A a _⟩⟩

theorem first_differential (a : A) :
    OneForms.IntegralOneForms.equiv R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A 0 ((equiv R A).symm a)) =
      KaehlerDifferential.D R A a := by
  have h : (equiv R A).symm a = fromZero R A a := by
    apply (equiv R A).injective
    exact (LinearEquiv.apply_symm_apply (equiv R A) a).trans
      (by rw [fromZero_apply]; exact (toZero_symbol R A a _).symm)
  rw [h, fromZero_apply, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential_symbol]
  change OneForms.IntegralOneForms.toOne R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 _) = _
  rw [OneForms.IntegralOneForms.toOne_symbol, one_smul]
  rfl

variable {R A}

theorem naturality {B C : CommAlgCat.{u} R} (f : B ⟶ C) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B 0) :
    equiv R C (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f 0 ω) = f (equiv R B ω) := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R B 0) ω
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single v a =>
    change toZero R C (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f 0 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B a v)) =
      f (toZero R B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B a v))
    rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, toZero_symbol, toZero_symbol]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ZeroForms.IntegralZeroForms
