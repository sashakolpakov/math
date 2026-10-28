import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectIso
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsKernel

/-! # Twisted Sections Detect Morphism -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectMorphism

noncomputable section

open _root_.MvPolynomial

/-! Positive-twist global sections detect zero morphisms of coherent sheaves. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsKernel
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem finiteType_hom_eq_zero_of_eventually_twistedSections_eq_zero [IsNoetherianRing R]
    {M N : (Proj (homogeneousSubmodule σ R)).Modules}
    [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent]
    (f : M ⟶ N) (j : σ) (b : ℕ)
    (hb : ∀ n : ℕ, b ≤ n → ∀ x,
      (((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map f).app ⊤) x = 0) :
    f = 0 := by
  have := Quasicoherent.Scheme.Modules.isQuasicoherent_kernel f
  have : Epi (kernel.ι f) :=
    TwistedSectionsDetectIso.MvPolynomial.finiteType_epi_of_eventually_twistedSections_surjective (kernel.ι f) j b (by
      intro n hn x
      let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
      obtain ⟨y, hy⟩ := GlobalSectionsKernel.exists_globalSection_kernel_preimage (F.map f) x (hb n hn x)
      refine ⟨((PreservesKernel.iso F f).inv).app ⊤ y, ?_⟩
      change ((PreservesKernel.iso F f).inv ≫ F.map (kernel.ι f)).app ⊤ y = x
      rw [PreservesKernel.iso_inv_ι]
      exact hy)
  exact zero_of_epi_comp (kernel.ι f) (kernel.condition f)

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectMorphism
