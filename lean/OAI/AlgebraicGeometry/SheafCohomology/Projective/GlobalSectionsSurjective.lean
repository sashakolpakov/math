import OAI.AlgebraicGeometry.SheafCohomology.Projective.SerreVanishing
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechVanishingTransfer
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseGlobalSectionsExact

/-! # Global Sections Surjective -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsSurjective

noncomputable section

open _root_.MvPolynomial

/-! Sufficiently positive projective twists make coherent epimorphisms surjective on sections. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace MonoidalCategory
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance projectiveSectionsMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

theorem finiteType_eventually_projectiveTwist_HOne_vanish [IsNoetherianRing R]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      Subsingleton (AffineH.Projective.H
        (M ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) 1) := by
  obtain ⟨b, hb⟩ := SerreVanishing.MvPolynomial.finiteType_eventually_orderedBaseCechComplex_exactAt_succ M j 0
  refine ⟨b, fun n hn => ?_⟩
  have : (M ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).IsQuasicoherent :=
    PositiveTwistEquivalence.MvPolynomial.moduleTensorCoordinateHyperplanePoleSheafPower_isQuasicoherent M j n
  exact BaseCechVanishingTransfer.orderedBaseCech_exactAt_subsingleton_H (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    _ (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (IsOpenCover.mk (StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ)))
    (StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R)) 1 (hb n hn)

theorem finiteType_epi_eventually_projectiveTwist_sections_surjective [IsNoetherianRing R]
    {M N : (Proj (homogeneousSubmodule σ R)).Modules}
    [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] (j : σ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      Function.Surjective
        (((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map f).app ⊤) := by
  have : LocallyOfFiniteType (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) :=
    MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType
  have : IsLocallyNoetherian (Proj (homogeneousSubmodule σ R)) :=
    LocallyOfFiniteType.isLocallyNoetherian (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  have : (kernel f).IsQuasicoherent := Quasicoherent.Scheme.Modules.isQuasicoherent_kernel f
  have : (kernel f).IsFiniteType := Quasicoherent.Scheme.Modules.isFiniteType_kernel f
  obtain ⟨b, hb⟩ := finiteType_eventually_projectiveTwist_HOne_vanish (kernel f) j
  let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hT : T.ShortExact := ShortComplex.ShortExact.mk (ShortComplex.kernelSequence_exact f)
  refine ⟨b, fun n hn => ?_⟩
  let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
  have hTF : (T.map F).ShortExact := hT.map_of_exact F
  have : Subsingleton (AffineH.Projective.H (T.map F).X₁ 1) := hb n hn
  exact BaseGlobalSectionsExact.globalSections_surjective_of_HOne_vanish hTF

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsSurjective
