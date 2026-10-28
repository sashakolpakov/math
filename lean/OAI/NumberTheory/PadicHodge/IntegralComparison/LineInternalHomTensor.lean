import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleEvaluation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections

/-! # Line Internal Hom Tensor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LineInternalHomTensor

noncomputable section

/-! For actual invertible sheaves, internal Hom is tensoring the target
with an inverse of the source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleEvaluation.Construction OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections

universe u

variable {X : Scheme.{u}}

local instance (Y : Scheme.{u}) : MonoidalCategory Y.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory Y

theorem isLineBundle_of_isInvertible {M : X.Modules} (hM : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible M) :
    ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M := by
  intro x
  obtain ⟨ι, U, hU, he⟩ := hM
  have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨U i, hi, he i⟩

def tensorEvaluationIso (M N : X.Modules) (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N) :
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N ⊗ M ≅ N :=
  AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalTensorObjIso (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N) M ≪≫ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleEvaluation.Construction.lineBundleHomEvaluationIso hM hN

def inverseTensorIso (M N P : X.Modules) (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N)
    (e : M ⊗ P ≅ 𝟙_ X.Modules) : ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N ≅ N ⊗ P :=
  (ρ_ (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N)).symm ≪≫
    (Iso.refl (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N) ⊗ᵢ e.symm) ≪≫
    (α_ (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N) M P).symm ≪≫
    (tensorEvaluationIso M N hM hN ⊗ᵢ Iso.refl P)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LineInternalHomTensor
