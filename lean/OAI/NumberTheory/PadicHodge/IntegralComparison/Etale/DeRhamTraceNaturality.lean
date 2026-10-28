import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTrace
import Mathlib.RingTheory.Localization.NormTrace

/-! # De Rham Trace Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTraceNaturality

noncomputable section

/-! The native étale de Rham trace is independent of the finite free basis
and commutes with restrictions to common-coordinate localizations. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u v w

section Extensionality

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]
  [Algebra.FormallyEtale (MvPolynomial σ R) A] [Fintype σ] [LinearOrder σ]

theorem formMap_ext (n : ℕ) {M : Type u} [AddCommGroup M] [Module R M]
    (f g : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₗ[R] M)
    (h : ∀ (a : A) (v : Fin n → σ),
      f (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ ∘ v)) =
        g (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ ∘ v))) :
    f = g := by
  have he : f.comp ((CoordinateComplexIso.iso R A σ).hom.f n).hom =
      g.comp ((CoordinateComplexIso.iso R A σ).hom.f n).hom := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext_on (AlgebraicGeometry.Crystalline.Cohomology.ExteriorCoordinate.ExteriorCoordinateProjection.word_span R σ n)
    rintro _ ⟨v, rfl⟩
    change f ((CoordinateComplexIso.iso R A σ).hom.f n
      (a ⊗ₜ[R] exteriorPower.ιMulti R n (fun i => Finsupp.single (v i) 1))) =
        g ((CoordinateComplexIso.iso R A σ).hom.f n
          (a ⊗ₜ[R] exteriorPower.ιMulti R n (fun i => Finsupp.single (v i) 1)))
    rw [CoordinateComplexIso.word]
    exact h a v
  apply LinearMap.ext
  intro ω
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((CoordinateComplexIso.iso R A σ).hom.f n)).mp inferInstance ω
  exact LinearMap.congr_fun he z

theorem complexMap_ext {M : CochainComplex (ModuleCat R) ℕ}
    (f g : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A ⟶ M)
    (h : ∀ (n : ℕ) (a : A) (v : Fin n → σ),
      f.f n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ ∘ v)) =
        g.f n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ ∘ v))) :
    f = g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact formMap_ext R A σ n (f.f n).hom (g.f n).hom (h n)

end Extensionality

section Basis

variable (R A B σ : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Algebra (MvPolynomial σ R) A] [Algebra (MvPolynomial σ R) B]
  [IsScalarTower R (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) B]
  [IsScalarTower (MvPolynomial σ R) A B]
  [Algebra.FormallyEtale (MvPolynomial σ R) A]
  [Algebra.FormallyEtale (MvPolynomial σ R) B]
  [Fintype σ] [LinearOrder σ]

omit [IsScalarTower R (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) B]
    [Algebra.FormallyEtale (MvPolynomial σ R) A]
    [Algebra.FormallyEtale (MvPolynomial σ R) B] [Fintype σ] [LinearOrder σ] in
theorem pullback_coordinate_symbol (n : ℕ) (a : A) (v : Fin n → σ) :
    (DeRhamTrace.pullback R A B).f n
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ ∘ v)) =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B (algebraMap A B a)
      (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R B σ ∘ v) := by
  change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)) n _ = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol]
  congr 1
  exact funext (fun i => DeRhamTrace.coordinate_map R A B σ (v i))

theorem trace_basis_independent {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι A B) (c : Module.Basis κ A B) :
    DeRhamTrace.trace R A B σ b = DeRhamTrace.trace R A B σ c := by
  apply complexMap_ext R B σ
  intro n x v
  rw [DeRhamTrace.trace_coordinate_symbol, DeRhamTrace.trace_coordinate_symbol]

end Basis

variable (R A B C D σ : Type u) [CommRing R] [CommRing A] [CommRing B]
  [CommRing C] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  [Algebra A B] [Algebra A C] [Algebra B D] [Algebra C D] [Algebra A D]
  [IsScalarTower R A B] [IsScalarTower R A C] [IsScalarTower R B D]
  [IsScalarTower R C D] [IsScalarTower A B D] [IsScalarTower A C D]
  [Algebra (MvPolynomial σ R) A] [Algebra (MvPolynomial σ R) B]
  [Algebra (MvPolynomial σ R) C] [Algebra (MvPolynomial σ R) D]
  [IsScalarTower R (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) B]
  [IsScalarTower R (MvPolynomial σ R) C] [IsScalarTower R (MvPolynomial σ R) D]
  [IsScalarTower (MvPolynomial σ R) A B] [IsScalarTower (MvPolynomial σ R) A C]
  [IsScalarTower (MvPolynomial σ R) B D] [IsScalarTower (MvPolynomial σ R) C D]
  [Algebra.FormallyEtale (MvPolynomial σ R) A]
  [Algebra.FormallyEtale (MvPolynomial σ R) B]
  [Algebra.FormallyEtale (MvPolynomial σ R) C]
  [Algebra.FormallyEtale (MvPolynomial σ R) D]
  [Fintype σ] [LinearOrder σ]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  (b : Module.Basis ι A B) (c : Module.Basis κ C D)
  (S : Submonoid A) [IsLocalization S C]
  [IsLocalization (Algebra.algebraMapSubmonoid B S) D]

include S in
theorem trace_localization :
    DeRhamTrace.trace R A B σ b ≫ DeRhamTrace.pullback R A C =
      DeRhamTrace.pullback R B D ≫ DeRhamTrace.trace R C D σ c := by
  have : Module.Free A B := Module.Free.of_basis b
  have : Module.Finite A B := Module.Finite.of_basis b
  apply complexMap_ext R B σ
  intro n x v
  change (DeRhamTrace.pullback R A C).f n ((DeRhamTrace.trace R A B σ b).f n _) =
    (DeRhamTrace.trace R C D σ c).f n ((DeRhamTrace.pullback R B D).f n _)
  rw [DeRhamTrace.trace_coordinate_symbol, pullback_coordinate_symbol R A C σ,
    pullback_coordinate_symbol R B D σ, DeRhamTrace.trace_coordinate_symbol]
  rw [Algebra.trace_localization A S x]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTraceNaturality
