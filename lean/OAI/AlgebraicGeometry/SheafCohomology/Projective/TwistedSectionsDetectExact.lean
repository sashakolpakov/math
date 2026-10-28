import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectIso

/-! # Twisted Sections Detect Exact -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectExact

noncomputable section

open _root_.MvPolynomial

/-! Exactness on all sufficiently positive global sections detects actual sheaf exactness. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem finiteType_exact_of_eventually_twistedSections_exact [IsNoetherianRing R]
    {L M N : (Proj (homogeneousSubmodule σ R)).Modules}
    [L.IsQuasicoherent] [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent]
    (f : L ⟶ M) (g : M ⟶ N) (hfg : f ≫ g = 0) (j : σ) (b : ℕ)
    (hb : ∀ n : ℕ, b ≤ n → Function.Exact
      (((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map f).app ⊤)
      (((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map g).app ⊤)) :
    (ShortComplex.mk f g hfg).Exact := by
  have : LocallyOfFiniteType (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) :=
    MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType
  have : IsLocallyNoetherian (Proj (homogeneousSubmodule σ R)) :=
    LocallyOfFiniteType.isLocallyNoetherian (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  have := Quasicoherent.Scheme.Modules.isQuasicoherent_kernel g
  have := Quasicoherent.Scheme.Modules.isFiniteType_kernel g
  apply (ShortComplex.mk f g hfg).exact_iff_epi_kernel_lift.mpr
  apply TwistedSectionsDetectIso.MvPolynomial.finiteType_epi_of_eventually_twistedSections_surjective (kernel.lift g f hfg) j b
  intro n hn x
  let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
  let k := F.map (kernel.ι g)
  have : Mono k := F.map_mono _
  have hcomp : k ≫ F.map g = 0 := by
    dsimp only [k]
    rw [← F.map_comp, kernel.condition, F.map_zero]
  have hzero : (F.map g).app ⊤ (k.app ⊤ x) = 0 := by
    change (k ≫ F.map g).app ⊤ x = 0
    rw [hcomp]
    rfl
  obtain ⟨y, hy⟩ := (hb n hn (k.app ⊤ x)).mp hzero
  refine ⟨y, ?_⟩
  apply GlobalSectionsMono.globalSections_injective_of_mono k
  change (F.map (kernel.lift g f hfg) ≫ F.map (kernel.ι g)).app ⊤ y = k.app ⊤ x
  rw [← F.map_comp, kernel.lift_ι]
  exact hy

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectExact
