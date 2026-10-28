import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectZero
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsMono
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsSurjective

/-! # Twisted Sections Detect Mono -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectMono

noncomputable section

open _root_.MvPolynomial

/-! Eventual injectivity on positive-twist sections detects sheaf monomorphisms. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsMono
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance twistedMonoDetectionMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

theorem finiteType_mono_of_eventually_twistedSections_injective [IsNoetherianRing R]
    {M N : (Proj (homogeneousSubmodule σ R)).Modules}
    [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent]
    (f : M ⟶ N) (j : σ) (b : ℕ)
    (hb : ∀ n : ℕ, b ≤ n → Function.Injective
      (((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map f).app ⊤)) :
    Mono f := by
  have : LocallyOfFiniteType (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) :=
    MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType
  have : IsLocallyNoetherian (Proj (homogeneousSubmodule σ R)) :=
    LocallyOfFiniteType.isLocallyNoetherian (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  have : (kernel f).IsQuasicoherent := Quasicoherent.Scheme.Modules.isQuasicoherent_kernel f
  have : (kernel f).IsFiniteType := Quasicoherent.Scheme.Modules.isFiniteType_kernel f
  apply Preadditive.mono_of_isZero_kernel f
  apply TwistedSectionsDetectZero.MvPolynomial.finiteType_isZero_of_eventually_twistedSections_subsingleton (kernel f) j b
  intro n hn
  let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
  let g := F.map (kernel.ι f)
  have : Mono g := F.map_mono _
  have hg := GlobalSectionsMono.globalSections_injective_of_mono g
  have hcomp : g ≫ F.map f = 0 := by
    dsimp only [g]
    rw [← F.map_comp, kernel.condition, F.map_zero]
  have hzero (x : Γ(F.obj (kernel f), ⊤)) : (F.map f).app ⊤ (g.app ⊤ x) = 0 := by
    change (g ≫ F.map f).app ⊤ x = 0
    rw [hcomp]
    rfl
  constructor
  intro x y
  apply hg
  apply hb n hn
  exact (hzero x).trans (hzero y).symm

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectMono
