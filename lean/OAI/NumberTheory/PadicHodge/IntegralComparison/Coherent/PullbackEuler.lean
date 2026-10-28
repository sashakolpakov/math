import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.EulerFunctoriality
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback

/-! # Pullback Euler -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.PullbackEuler.ProjectiveK

noncomputable section

/-! The Euler characteristic of an actual affine pullback of a line
bundle is computed by the actual direct image of the structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u
attribute [local instance] MvPolynomial.gradedAlgebra AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

variable {K : Type u} [Field K] {r : ℕ} {A : Scheme.{u}} [A.IsSeparated]
  (f : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
  [IsClosedImmersion f]

theorem coherentEuler_pullback_lineBundle
    (ρ : A ⟶ Spec (CommRingCat.of K))
    (hf : f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = ρ)
    (g : A ⟶ A) [IsAffineHom g] (hg : g ≫ ρ = ρ) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A) :
    EulerIndex.ProjectiveK.coherentEuler f (L.pullback g).sheaf =
      EulerIndex.ProjectiveK.coherentEuler f ((Scheme.Modules.pushforward g).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A) ⊗ L.sheaf) := by
  have : (L.pullback g).sheaf.IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (L.pullback g))
  let e := AlgebraicGeometry.FormalGeometry.Completion.LineBundleProjection.Construction.lineBundleProjectionIso g L (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A) ≪≫
    (Scheme.Modules.pushforward g).mapIso (AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient.Dimension.structureModuleTensorLeftIso (L.pullback g).sheaf)
  calc
    EulerIndex.ProjectiveK.coherentEuler f (L.pullback g).sheaf =
        EulerIndex.ProjectiveK.coherentEuler f ((Scheme.Modules.pushforward g).obj (L.pullback g).sheaf) :=
      (EulerFunctoriality.ProjectiveK.coherentEuler_pushforward_of_affine f ρ hf g hg (L.pullback g).sheaf).symm
    _ = _ := (EulerIndex.ProjectiveK.coherentEuler_eq_of_iso f e).symm

theorem coherentEuler_pullback_tensorPower
    (ρ : A ⟶ Spec (CommRingCat.of K))
    (hf : f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = ρ)
    (g : A ⟶ A) [IsAffineHom g] (hg : g ≫ ρ = ρ) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A) (n : ℕ) :
    EulerIndex.ProjectiveK.coherentEuler f ((L.pullback g).tensorPower n).sheaf =
      EulerIndex.ProjectiveK.coherentEuler f ((Scheme.Modules.pushforward g).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A) ⊗
        (L.tensorPower n).sheaf) := by
  calc
    EulerIndex.ProjectiveK.coherentEuler f ((L.pullback g).tensorPower n).sheaf =
        EulerIndex.ProjectiveK.coherentEuler f ((L.tensorPower n).pullback g).sheaf :=
      EulerIndex.ProjectiveK.coherentEuler_eq_of_iso f (AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap.iso g L n).symm
    _ = _ := coherentEuler_pullback_lineBundle f ρ hf g hg (L.tensorPower n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.PullbackEuler.ProjectiveK
