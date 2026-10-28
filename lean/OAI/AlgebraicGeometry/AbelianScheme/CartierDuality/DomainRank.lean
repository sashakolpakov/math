import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Algebraic.Integral

/-! # Domain Rank -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DomainRank.Construction.Schemes

noncomputable section

/-! Finite-flat rank calculations over integral affine schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- Localization does not change module rank over a domain. -/
theorem rankAtStalk_eq_finrank_of_domain
    (R M : Type u) [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) : Module.rankAtStalk M p = Module.finrank R M := by
  change Module.finrank (Localization.AtPrime p.asIdeal)
    (LocalizedModule p.asIdeal.primeCompl M) = _
  exact (IsLocalization.finrank_eq (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl
    p.asIdeal.primeCompl_le_nonZeroDivisors).trans
      (IsLocalizedModule.finrank_eq p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) p.asIdeal.primeCompl_le_nonZeroDivisors)

/-- A finite flat affine morphism over an integral base has its coordinate-module rank. -/
theorem spec_finrank_domain
    (R T : Type u) [CommRing R] [IsDomain R] [CommRing T] [Algebra R T]
    [Module.Finite R T] [Module.Flat R T] (p : Spec (.of R)) :
    (Spec.map (CommRingCat.ofHom (algebraMap R T))).finrank p = Module.finrank R T :=
  (Scheme.Hom.finrank_SpecMap_algebraMap R T p).trans (rankAtStalk_eq_finrank_of_domain R T p)

/-- The native scheme rank is computed by global coordinates on integral affine targets. -/
theorem affine_finrank_domain {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (y : Y) :
    f.finrank y =
      @Module.finrank Γ(Y, ⊤) Γ(X, ⊤) _ _ f.appTop.hom.toAlgebra.toModule := by
  have : IsFinite (Spec.map f.appTop) := (IsFinite.SpecMap_iff _).mpr f.finite_appTop
  have : Flat (Spec.map f.appTop) := Flat.SpecMap_iff.mpr f.flat_appTop
  have sq : IsPullback X.isoSpec.hom f (Spec.map f.appTop) Y.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality f⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq y,
    Scheme.Hom.finrank_SpecMap_eq_finrank f.finite_appTop f.flat_appTop]
  let := f.appTop.hom.toAlgebra
  exact rankAtStalk_eq_finrank_of_domain Γ(Y, ⊤) Γ(X, ⊤) (Y.isoSpec.hom y)

/-- The tower law computes degrees on integral affine schemes, retaining inseparable degree. -/
theorem affine_finrank_comp {X Y Z : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsAffine Z] [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [Flat f] [Surjective f]
    [IsFinite g] [Flat g] (y : Y) (z : Z) :
    (f ≫ g).finrank z = g.finrank z * f.finrank y := by
  let := f.appTop.hom.toAlgebra
  let := g.appTop.hom.toAlgebra
  let := (f ≫ g).appTop.hom.toAlgebra
  have : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) Γ(X, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (Scheme.Hom.comp_appTop f g))
  have hf : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩
  have : Module.FaithfullyFlat Γ(Y, ⊤) Γ(X, ⊤) := hf
  rw [affine_finrank_domain (f ≫ g), affine_finrank_domain f, affine_finrank_domain g]
  exact (Module.finrank_mul_finrank' (R := Γ(Z, ⊤)) (S := Γ(Y, ⊤)) Γ(X, ⊤)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DomainRank.Construction.Schemes
