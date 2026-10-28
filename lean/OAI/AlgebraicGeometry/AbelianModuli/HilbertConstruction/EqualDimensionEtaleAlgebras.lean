import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EtaleCotangentCriterion
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.OrzechProperty

/-! # Equal Dimension Etale Algebras -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualDimensionEtaleAlgebras

noncomputable section

/-! An unramified map between standard smooth algebras of the same relative dimension is etale. -/

open _root_.Algebra TensorProduct
open scoped TensorProduct

universe u v w

variable (R : Type u) (S : Type v) (T : Type w)
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

theorem formallyEtale_of_standardSmooth_equal_dimension (d : ℕ)
    [IsStandardSmoothOfRelativeDimension d R S] [IsStandardSmoothOfRelativeDimension d R T]
    [FormallyUnramified S T] : FormallyEtale S T := by
  rcases subsingleton_or_nontrivial T with hT | hT
  · exact ⟨inferInstance, inferInstance⟩
  have : Nontrivial S := (algebraMap S T).domain_nontrivial
  have : IsStandardSmooth R S := IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have : IsStandardSmooth R T := IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have hs : Module.finrank S Ω[S⁄R] = d := by
    rw [Module.finrank, IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential d]
    simp
  have ht : Module.finrank T Ω[T⁄R] = d := by
    rw [Module.finrank, IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential d]
    simp
  let e : (T ⊗[S] Ω[S⁄R]) ≃ₗ[T] Ω[T⁄R] := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_baseChange, hs, ht])
  have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange R S T) :=
    fun x => (KaehlerDifferential.exact_mapBaseChange_map R S T x).mp (Subsingleton.elim _ _)
  exact EtaleCotangentCriterion.formallyEtale_of_cotangent_injective R S T
    (OrzechProperty.injective_of_surjective_of_injective e.toLinearMap
      (KaehlerDifferential.mapBaseChange R S T) e.injective hsurj)

theorem etale_of_standardSmooth_equal_dimension (d : ℕ)
    [IsStandardSmoothOfRelativeDimension d R S] [IsStandardSmoothOfRelativeDimension d R T]
    [FormallyUnramified S T] : Etale S T := by
  have : IsStandardSmooth R S := IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have : IsStandardSmooth R T := IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have : FinitePresentation S T := FinitePresentation.of_restrict_scalars_finitePresentation R S T
  exact {
    formallyEtale := formallyEtale_of_standardSmooth_equal_dimension R S T d
    finitePresentation := inferInstance }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualDimensionEtaleAlgebras
