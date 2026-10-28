import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionEvaluationNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections

/-! # Section Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.SectionEvaluation

noncomputable section

/-! The actual source-section evaluation is an algebra map over the
actual target section ring, using the target-section quotient action. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : Y ⟶ X)
  (s : Spec (CommRingCat.of R) ⟶ Y.left) (hs : s ≫ Y.hom = 𝟙 _)
  (U : X.left.Opens) (hU : ⊤ ≤ (s ≫ f.left) ⁻¹ᵁ U)

abbrev targetRing : Type u := Γ(X.left,U)
abbrev sourceRing : Type u := Γ(Y.left,f.left ⁻¹ᵁ U)
local instance targetBase : Algebra R (targetRing R X U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
local instance sourceBase : Algebra R (sourceRing R X Y f U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y (f.left ⁻¹ᵁ U)
local instance sourceAlgebra : Algebra (targetRing R X U) (sourceRing R X Y f U) :=
  ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule.Construction.affinePreimageSectionAlgebra f.left U

def targetEvaluation : targetRing R X U →ₐ[R] R :=
  Intrinsic.SectionEvaluation.evaluation R X (s ≫ f.left)
    (SectionEvaluationNaturality.image_retraction R Y X f s hs) U hU

@[instance_reducible] def quotientAlgebra : Algebra (targetRing R X U) R :=
  (targetEvaluation R X Y f s hs U hU).toRingHom.toAlgebra

def evaluation :
    letI := quotientAlgebra R X Y f s hs U hU
    sourceRing R X Y f U →ₐ[targetRing R X U] R := by
  letI := quotientAlgebra R X Y f s hs U hU
  exact {
    toRingHom := (Intrinsic.SectionEvaluation.evaluation R Y s hs (f.left ⁻¹ᵁ U) hU).toRingHom
    commutes' a := SectionEvaluationNaturality.pullback R Y X f s hs U hU a }

theorem evaluation_apply (a : sourceRing R X Y f U) :
    evaluation R X Y f s hs U hU a =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom (s.appLE (f.left ⁻¹ᵁ U) ⊤ hU a) := rfl

theorem target_apply (a : targetRing R X U) :
    letI := quotientAlgebra R X Y f s hs U hU
    algebraMap (targetRing R X U) R a = targetEvaluation R X Y f s hs U hU a := rfl

theorem base (a : R) :
    letI := quotientAlgebra R X Y f s hs U hU
    algebraMap (targetRing R X U) R (algebraMap R (targetRing R X U) a) = a := by
  let := quotientAlgebra R X Y f s hs U hU
  exact (targetEvaluation R X Y f s hs U hU).commutes a

theorem surjective :
    letI := quotientAlgebra R X Y f s hs U hU
    Function.Surjective (algebraMap (targetRing R X U) R) := by
  let := quotientAlgebra R X Y f s hs U hU
  exact fun a => ⟨algebraMap R (targetRing R X U) a, base R X Y f s hs U hU a⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.SectionEvaluation
