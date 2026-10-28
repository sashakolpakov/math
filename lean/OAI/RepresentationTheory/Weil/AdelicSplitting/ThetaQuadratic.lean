import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest
import OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterProduct

/-! # Theta Quadratic -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! The prescribed rational quadratic generators preserve the actual
theta sum, by the principal product formula for the supplied character. -/

open scoped Classical _root_.NumberField

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
  (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hu : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ)
  (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)

theorem ThetaQuadratic.Construction.quadratic_localize_rational (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) (q : Fin N → F) (v : ArchimedeanAdeles.Construction.Places F) :
    Local.FunctionsMetaplectic.Construction.quadratic (QuadraticGenerators.Construction.localizeQuadratic F N B v).val (fun i => ArchimedeanAdeles.Construction.rationalScalar F v (q i)) =
      ArchimedeanAdeles.Construction.rationalScalar F v (Local.FunctionsMetaplectic.Construction.quadratic B.val q) := by
  simp only [Local.FunctionsMetaplectic.Construction.quadratic, QuadraticGenerators.Construction.localizeQuadratic, Matrix.map_apply, map_div₀, map_ofNat,
    map_sum, map_mul]

include hc hp in
theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.quadratic_rational_value
    (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalQuadratic F N ψ B a)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (q : Fin N → F) :
    (f.act F N ψ a).value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)) =
      f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)) := by
  have hv (v : ArchimedeanAdeles.Construction.Places F) :
      (f.act F N ψ a).localValue F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)) v =
        Characters.Construction.localAdditiveCharacter F ψ v (ArchimedeanAdeles.Construction.rationalScalar F v (Local.FunctionsMetaplectic.Construction.quadratic B.val q)) *
          f.localValue F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)) v := by
    change (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v) (f v)).val
        (fun i => ArchimedeanAdeles.Construction.rationalScalar F v (q i)) = _
    rw [ha.2]
    congr 1
    exact congrArg (Characters.Construction.localAdditiveCharacter F ψ v) (ThetaQuadratic.Construction.quadratic_localize_rational F N B q v)
  have hprod := (CharacterProduct.Construction.localAdditiveCharacter_principal_hasProd F ψ hc hp (Local.FunctionsMetaplectic.Construction.quadratic B.val q)).mul
    (f.localValue_hasProd F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)))
  simp only [one_mul] at hprod
  have hprod' : HasProd ((f.act F N ψ a).localValue F N
      (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))) (f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))) := by
    exact hprod.congr_fun hv
  exact ((f.act F N ψ a).localValue_hasProd F N _).unique hprod'

include hc hp in
theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_rational_quadratic
    (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalQuadratic F N ψ B a)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    (f.act F N ψ a).theta F N = f.theta F N := by
  apply tsum_congr
  exact f.quadratic_rational_value F N ψ hc hp B a ha

include hp in
theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_quadratic_family (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    (f.act F N ψ (QuadraticGenerators.Construction.rationalQuadraticFamily F N ψ hu hc B)).theta F N = f.theta F N :=
  f.theta_rational_quadratic F N ψ hc hp B _ (QuadraticGenerators.Construction.rationalQuadraticFamily_spec F N ψ hu hc B)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
