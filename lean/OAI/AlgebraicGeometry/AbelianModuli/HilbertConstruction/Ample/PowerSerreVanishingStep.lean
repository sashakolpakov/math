import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.SerreVanishing

/-! # Power Serre Vanishing Step -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerSerreVanishingStep

noncomputable section

/-! Ampleness constructs the positive degree used by the Serre-vanishing step. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem ample_tensorPowers_vanishing_step
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] (L : Line.Bundles.LineBundle X) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ∀ (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType],
      ∃ B : ℕ, ∀ m : ℕ, B ≤ m → ∀ q : ℕ,
        IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap f) (q + 1)).obj
          (Tensor.ProductSheaf.tensorModule M (L.tensorPower (m * d)).sheaf)) := by
  obtain ⟨E⟩ := hL.exists_powerProjectiveEmbedding f
  exact ⟨E.degree, E.degree_pos, fun M _ _ ↦ E.tensorPowers_eventually_vanish M⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerSerreVanishingStep
