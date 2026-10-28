import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison
import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticSwap
import OAI.RepresentationTheory.Weil.Local.RealCover

/-! # Schrodinger Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerAction.CM

noncomputable section

/-! Transport LocalWeil's constructed real metaplectic group to PoissonAutomorphy's actual
test functions and momentum-position convention. The resulting action
and symplectic projection are genuine homomorphisms. -/

open scoped Classical
open OAI.RepresentationTheory.Weil.Local.RealCover.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison.CM OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization

abbrev RealMp (n : ℕ) := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)

def action (n : ℕ) : RealMp n →* (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) where
  toFun g := (SchwartzComparison.CM.tests n).trans ((RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g).trans (SchwartzComparison.CM.tests n).symm)
  map_one' := by
    apply LinearEquiv.ext
    intro f
    change (SchwartzComparison.CM.tests n).symm (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) 1 (SchwartzComparison.CM.tests n f)) = f
    rw [map_one]
    exact (SchwartzComparison.CM.tests n).symm_apply_apply f
  map_mul' g h := by
    apply LinearEquiv.ext
    intro f
    change (SchwartzComparison.CM.tests n).symm (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (g * h) (SchwartzComparison.CM.tests n f)) =
      (SchwartzComparison.CM.tests n).symm (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g
        (SchwartzComparison.CM.tests n ((SchwartzComparison.CM.tests n).symm (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) h (SchwartzComparison.CM.tests n f)))))
    rw [map_mul, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]

theorem action_apply (n : ℕ) (g : RealMp n) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (x : Fin n → ℝ) :
    (action n g f).val x = (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g (SchwartzComparison.CM.tests n f)).val x := rfl

def projection (n : ℕ) : RealMp n →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℝ :=
  RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom.comp (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1))

theorem swap_involutive {n : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℝ) : RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom g) = g := by
  apply Subtype.ext
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap * (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap) * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap = g.val
  have h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap * (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap) * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap) * g.val * (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap) := by noncomm_ring
  rw [h, RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.coordinateSwap_square, Matrix.one_mul, Matrix.mul_one]

theorem projection_surjective (n : ℕ) : Function.Surjective (projection n) := by
  intro g
  obtain ⟨h, hh⟩ := RepresentationTheory.Weil.Local.RealCover.Construction.real_metaplecticProjection_surjective_standard n (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom g)
  refine ⟨h, ?_⟩
  change RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) h) = g
  rw [hh, swap_involutive]

theorem action_intertwines (n : ℕ) (g : RealMp n) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (projection n g) (action n g) := by
  intro p q f h hh x
  have hin : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (Sum.elim q p) (SchwartzComparison.CM.tests n f) (SchwartzComparison.CM.tests n h) := by
    funext y
    exact (hh y).trans (SchwartzComparison.CM.heisenberg_formula n p q f.val y)
  have hout := (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation_intertwines ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g (Sum.elim q p)
    (SchwartzComparison.CM.tests n f) (SchwartzComparison.CM.tests n h)).mp hin
  have he := congrFun hout x
  rw [action_apply]
  rw [SchwartzComparison.CM.heisenberg_formula]
  change _ = RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)
    (Sum.elim (fun i => (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g)).val.mulVec
      (Sum.elim p q) (.inr i))
      (fun i => (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g)).val.mulVec
        (Sum.elim p q) (.inl i))) (action n g f).val x
  simp only [RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom_action, RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.swapPhase, Sum.elim_inl, Sum.elim_inr]
  exact he

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerAction.CM
