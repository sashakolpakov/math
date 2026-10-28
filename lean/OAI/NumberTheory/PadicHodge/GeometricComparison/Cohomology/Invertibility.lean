import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.FrobeniusDefinition
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.Good

/-! # Invertibility -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Invertibility of the actual q-power crystalline Frobenius follows from the complete Cohomology proposition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Cohomology.Invertibility.bijective_of_pointwise {V W : Type*} (f g : V → W)
    (h : ∀ x, f x = g x) (hf : Function.Bijective f) : Function.Bijective g :=
  (congrArg Function.Bijective (funext h)).mp hf

theorem Cohomology.Invertibility.bijective_transport {V W : Type*} (e : V ≃ W) (T : V → V) (U : W → W)
    (h : ∀ x, e (T x) = U (e x)) (hT : Function.Bijective T) : Function.Bijective U := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    exact congrArg e (hT.1 (e.injective ((h a).trans (hxy.trans (h b).symm))))
  · intro y
    obtain ⟨a, ha⟩ := hT.2 (e.symm y)
    exact ⟨e a, (h a).symm.trans ((congrArg e ha).trans (e.apply_symm_apply y))⟩

def Cohomology.Invertibility.linearEquivOfBijective {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (T : V →ₗ[R] V) (h : Function.Bijective T) : V ≃ₗ[R] V := LinearEquiv.ofBijective T h

theorem Cohomology.Invertibility.linearEquivOfBijective_toLinearMap {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (T : V →ₗ[R] V) (h : Function.Bijective T) : (Cohomology.Invertibility.linearEquivOfBijective T h).toLinearMap = T := rfl

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.smallCrystallineFrobenius_bijective_of_Cohomology (hCohomology : Cohomology.Good.GoodReductionInput.{0}) :
    Function.Bijective A.smallCrystallineFrobenius := by
  let : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom
      (PadicInt.toZMod : ℤ_[q] →+* ZMod q)))).obj A.integral.scheme).hom := A.specialFiber.proper
  have h := (hCohomology q (DVR.PadicBase.dvr q) A.integral.scheme 1).choose_spec.2.2.1
  have hb := Cohomology.Invertibility.bijective_of_pointwise _ _
    (Cohomology.FrobeniusDefinition.CrystallineAdapter.e62Frobenius_eq_native q A.integral.scheme) h
  exact (Cohomology.FrobeniusDefinition.CrystallineAdapter.smallFrobenius_bijective_congr q
    (DVR.PadicBase.specialFiber_eq q A.integral.scheme)).mp hb

theorem Geometry.AbelianH1Model.crystallineFrobenius_bijective_of_Cohomology (hCohomology : Cohomology.Good.GoodReductionInput.{0}) :
    Function.Bijective A.crystallineFrobenius :=
  Cohomology.Invertibility.bijective_transport A.smallCrystallineEquiv.toEquiv A.smallCrystallineFrobenius A.crystallineFrobenius
    A.smallCrystallineEquiv_frobenius (A.smallCrystallineFrobenius_bijective_of_Cohomology hCohomology)

def Geometry.AbelianH1Model.crystallineFrobeniusEquiv (hCohomology : Cohomology.Good.GoodReductionInput.{0}) : A.Crystalline ≃ₗ[ℚ_[q]] A.Crystalline :=
  Cohomology.Invertibility.linearEquivOfBijective A.crystallineFrobenius (A.crystallineFrobenius_bijective_of_Cohomology hCohomology)

theorem Geometry.AbelianH1Model.crystallineFrobeniusEquiv_toLinearMap (hCohomology : Cohomology.Good.GoodReductionInput.{0}) :
    (A.crystallineFrobeniusEquiv hCohomology).toLinearMap = A.crystallineFrobenius :=
  Cohomology.Invertibility.linearEquivOfBijective_toLinearMap _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
