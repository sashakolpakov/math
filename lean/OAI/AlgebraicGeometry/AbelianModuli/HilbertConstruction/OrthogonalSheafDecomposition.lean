import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafSummands

/-! # Orthogonal Sheaf Decomposition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrthogonalSheafDecomposition

noncomputable section

/-! A finite complete family of orthogonal sheaf idempotents gives an actual biproduct decomposition through its equalizer summands. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v
instance moduleSheaf_hasFiniteBiproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {X : Scheme.{u}} {M : X.Modules} {I : Type v}

def orthogonalIdempotentSheafBicone (p : I → End M)
    (hp : ∀ i, p i ≫ p i = p i) (ho : ∀ i j, i ≠ j → p i ≫ p j = 0) :
    Bicone (fun i => IdempotentSheafSummands.idempotentSheafSummand (p i)) where
  pt := M
  π i := IdempotentSheafSummands.idempotentSheafRetraction (p i) (hp i)
  ι i := IdempotentSheafSummands.idempotentSheafInclusion (p i)
  ι_π i j := by
    classical
    by_cases h : i = j
    · subst j
      simpa using IdempotentSheafSummands.idempotentSheafInclusion_retraction (p i) (hp i)
    · simpa only [dite_eq_right h] using
        IdempotentSheafSummands.idempotentSheafInclusion_retraction_orthogonal (p i) (p j) (hp j) (ho i j h)

def orthogonalIdempotentSheafBilimit [Fintype I] (p : I → End M)
    (hp : ∀ i, p i ≫ p i = p i) (ho : ∀ i j, i ≠ j → p i ≫ p j = 0)
    (hs : ∑ i, p i = 𝟙 M) : (orthogonalIdempotentSheafBicone p hp ho).IsBilimit :=
  isBilimitOfTotal _ (by
    change ∑ i, IdempotentSheafSummands.idempotentSheafRetraction (p i) (hp i) ≫ IdempotentSheafSummands.idempotentSheafInclusion (p i) = 𝟙 M
    simpa only [IdempotentSheafSummands.idempotentSheafRetraction_inclusion] using hs)

def orthogonalIdempotentSheafIso [Fintype I] (p : I → End M)
    (hp : ∀ i, p i ≫ p i = p i) (ho : ∀ i j, i ≠ j → p i ≫ p j = 0)
    (hs : ∑ i, p i = 𝟙 M) : M ≅ ⨁ (fun i => IdempotentSheafSummands.idempotentSheafSummand (p i)) :=
  biproduct.uniqueUpToIso _ (orthogonalIdempotentSheafBilimit p hp ho hs)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrthogonalSheafDecomposition
