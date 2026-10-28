import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectMono
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoherentQuotientFiniteType

/-! # Twisted Sections Detect Iso -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectIso

noncomputable section

open _root_.MvPolynomial

/-! Eventual surjectivity and bijectivity on positive-twist sections detect sheaf maps. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance twistedIsoDetectionMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

theorem finiteType_epi_of_eventually_twistedSections_surjective [IsNoetherianRing R]
    {M N : (Proj (homogeneousSubmodule σ R)).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFiniteType]
    (f : M ⟶ N) (j : σ) (b : ℕ)
    (hb : ∀ n : ℕ, b ≤ n → Function.Surjective
      (((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map f).app ⊤)) :
    Epi f := by
  have := Quasicoherent.Scheme.Modules.isQuasicoherent_cokernel f
  have := CoherentQuotientFiniteType.Scheme.Modules.isFiniteType_cokernel f
  obtain ⟨c, hc⟩ := GlobalSectionsSurjective.MvPolynomial.finiteType_epi_eventually_projectiveTwist_sections_surjective (cokernel.π f) j
  apply Preadditive.epi_of_isZero_cokernel f
  apply TwistedSectionsDetectZero.MvPolynomial.finiteType_isZero_of_eventually_twistedSections_subsingleton (cokernel f) j (max b c)
  intro n hn
  let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
  have hcomp : F.map f ≫ F.map (cokernel.π f) = 0 := by
    rw [← F.map_comp, cokernel.condition, F.map_zero]
  have hzero (z : Γ(F.obj (cokernel f), ⊤)) : z = 0 := by
    obtain ⟨y, rfl⟩ := hc n ((le_max_right b c).trans hn) z
    obtain ⟨x, rfl⟩ := hb n ((le_max_left b c).trans hn) y
    change (F.map f ≫ F.map (cokernel.π f)).app ⊤ x = 0
    rw [hcomp]
    rfl
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

theorem finiteType_isIso_of_eventually_twistedSections_bijective [IsNoetherianRing R]
    {M N : (Proj (homogeneousSubmodule σ R)).Modules}
    [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
    (f : M ⟶ N) (j : σ) (b : ℕ)
    (hb : ∀ n : ℕ, b ≤ n → Function.Bijective
      (((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map f).app ⊤)) :
    IsIso f := by
  have := TwistedSectionsDetectMono.MvPolynomial.finiteType_mono_of_eventually_twistedSections_injective f j b (fun n hn => (hb n hn).1)
  have := finiteType_epi_of_eventually_twistedSections_surjective f j b (fun n hn => (hb n hn).2)
  exact isIso_of_mono_of_epi f

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectIso
