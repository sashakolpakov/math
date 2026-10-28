import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsSurjective
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation

/-! # Presentation Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentationSections

noncomputable section

open _root_.MvPolynomial

/-! Coherent presentations become actual global-section cokernel presentations after twisting. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem finiteType_exact_eventually_projectiveTwist_sections [IsNoetherianRing R]
    (T : ShortComplex (Proj (homogeneousSubmodule σ R)).Modules) (hT : T.Exact) [Epi T.g]
    [T.X₁.IsQuasicoherent] [T.X₁.IsFiniteType]
    [T.X₂.IsQuasicoherent] [T.X₂.IsFiniteType] [T.X₃.IsQuasicoherent] (j : σ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
      Function.Exact ((F.map T.f).app ⊤) ((F.map T.g).app ⊤) ∧
        Function.Surjective ((F.map T.g).app ⊤) := by
  have : (kernel T.g).IsQuasicoherent := Quasicoherent.Scheme.Modules.isQuasicoherent_kernel T.g
  let p := kernel.lift T.g T.f T.zero
  have : Epi p := (ShortComplex.exact_iff_epi_kernel_lift _).mp hT
  obtain ⟨b₁, hb₁⟩ := GlobalSectionsSurjective.MvPolynomial.finiteType_epi_eventually_projectiveTwist_sections_surjective p j
  obtain ⟨b₂, hb₂⟩ := GlobalSectionsSurjective.MvPolynomial.finiteType_epi_eventually_projectiveTwist_sections_surjective T.g j
  let K := ShortComplex.mk (kernel.ι T.g) T.g (kernel.condition T.g)
  have hK : K.ShortExact := { exact := ShortComplex.kernelSequence_exact T.g }
  refine ⟨max b₁ b₂, fun n hn => ?_⟩
  let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
  have hKF : (K.map F).ShortExact := hK.map_of_exact F
  have hp : Function.Surjective ((F.map p).app ⊤) := hb₁ n (le_trans (le_max_left _ _) hn)
  refine ⟨?_, hb₂ n (le_trans (le_max_right _ _) hn)⟩
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (BaseGlobalSectionsExact.globalSections_exact_of_shortExact hKF x).mp hx
    obtain ⟨z, hz⟩ := hp y
    refine ⟨z, ?_⟩
    have hcomp : F.map p ≫ F.map (kernel.ι T.g) = F.map T.f := by
      rw [← F.map_comp]
      exact congrArg F.map (kernel.lift_ι T.g T.f T.zero)
    have heval := congrArg (fun f => f.app ⊤ z) hcomp
    change (F.map (kernel.ι T.g)).app ⊤ ((F.map p).app ⊤ z) = (F.map T.f).app ⊤ z at heval
    rw [← heval, hz]
    exact hy
  · rintro ⟨y, rfl⟩
    have hz : F.map T.f ≫ F.map T.g = 0 := by rw [← F.map_comp, T.zero, F.map_zero]
    exact congrArg (fun f => f.app ⊤ y) hz

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentationSections
