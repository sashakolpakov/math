import OAI.RepresentationTheory.Theta.Geometric.HomogeneousSheafInjection
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductPicard

/-! # Parameter Separation -/

namespace OAI.RepresentationTheory.Theta.Geometric.Relative.ParameterSeparation

noncomputable section

/-! Monomorphy of the actual homogeneous parameter map separates its
relative Picard values on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u
theorem relativeValue_injective_of_homogeneous_mono
    {K : Type u} [Field K] {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))
    {P : Over (Spec (.of K))} (Q : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.scheme P)
    (hQ : A.IsHomogeneousPicardClass P (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.bundle))
    [Mono (ParameterizedHomogeneousPicard.homogeneousParameterMap A Q.bundle hQ)] (T : Over (Spec (.of K))) :
    Function.Injective (Q.relativeValue (T := T)) := by
  intro a b hab
  have h : ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A Q.bundle hQ a =
      ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A Q.bundle hQ b := by
    apply HomogeneousSheafInjection.homogeneousPicardSheafInclusion_injective A T
    rw [ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget, ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget]
    exact hab
  have hi := (CategoryTheory.mono_iff_injective
    ((ParameterizedHomogeneousPicard.homogeneousParameterMap A Q.bundle hQ).app (.op T))).mp inferInstance
  exact congrArg ULift.down (hi (a₁ := ULift.up a) (a₂ := ULift.up b) h)

end

end OAI.RepresentationTheory.Theta.Geometric.Relative.ParameterSeparation
