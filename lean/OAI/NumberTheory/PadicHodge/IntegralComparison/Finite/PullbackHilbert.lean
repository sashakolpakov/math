import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.EulerHilbert
import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.PullbackEuler
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PushforwardCoherence

/-! # Pullback Hilbert -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PullbackHilbert.ProjectiveK

noncomputable section

/-! For an actual finite self-map, the Euler polynomial of the pulled
back hyperplane bundle is the Hilbert polynomial of the actual direct
image of the structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u
attribute [local instance] MvPolynomial.gradedAlgebra AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

def coherentFinitePushforward {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g]
    (M : Coherent.KTheory.Projective.CoherentModule X) : Coherent.KTheory.Projective.CoherentModule Y where
  sheaf := (Scheme.Modules.pushforward g).obj M.sheaf
  quasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom g
  finiteType := PushforwardCoherence.finiteType g M.sheaf

variable {K : Type u} [Field K] [Infinite K] {r : ℕ} {A : Scheme.{u}}
  [IsIntegral A] [A.IsSeparated]
  (f : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
  [IsClosedImmersion f] (j : Fin (r + 1))

theorem finitePullback_euler_eq_hilbert
    (ρ : A ⟶ Spec (CommRingCat.of K))
    (hf : f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = ρ)
    (g : A ⟶ A) [IsFinite g] (hg : g ≫ ρ = ρ) (n : ℕ) :
    (Coherent.EulerIndex.ProjectiveK.coherentEuler f (((Coherent.EulerHilbert.ProjectiveK.projectiveLineBundle f j).pullback g).tensorPower n).sheaf : ℚ) =
      (Coherent.HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j
        (coherentFinitePushforward g (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A))).eval (n : ℚ) := by
  rw [Coherent.PullbackEuler.ProjectiveK.coherentEuler_pullback_tensorPower f ρ hf g hg (Coherent.EulerHilbert.ProjectiveK.projectiveLineBundle f j) n]
  rw [← Coherent.EulerHilbert.ProjectiveK.coherentProjectiveTwist_euler f j
    (coherentFinitePushforward g (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A)) n]
  let e := AlgebraicGeometry.SheafCohomology.Projective.UniversalPowers.Dimension.pullbackProjectiveTwistUniversalIso f j (Coherent.EulerHilbert.ProjectiveK.projectiveLineBundle f j) (Iso.refl _) n
  exact congrArg (fun z : ℤ => (z : ℚ))
    (Coherent.EulerIndex.ProjectiveK.coherentEuler_eq_of_iso f (Iso.refl _ ⊗ᵢ e.symm))

theorem polynomial_eq_finitePushforward_hilbert
    (ρ : A ⟶ Spec (CommRingCat.of K))
    (hf : f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = ρ)
    (g : A ⟶ A) [IsFinite g] (hg : g ≫ ρ = ρ)
    (P : Polynomial ℚ)
    (hP : ∀ n : ℕ, P.eval (n : ℚ) =
      (Coherent.EulerIndex.ProjectiveK.coherentEuler f (((Coherent.EulerHilbert.ProjectiveK.projectiveLineBundle f j).pullback g).tensorPower n).sheaf : ℚ)) :
    P = Coherent.HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j (coherentFinitePushforward g (Coherent.StructureDimension.ProjectiveK.coherentStructureModule A)) := by
  apply AlgebraicGeometry.FormalGeometry.Completion.EventualPolynomial.Construction.polynomial_eq_of_eventual_nat_eval _ _ 0
  intro n _
  exact (hP n).trans (finitePullback_euler_eq_hilbert f j ρ hf g hg n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PullbackHilbert.ProjectiveK
