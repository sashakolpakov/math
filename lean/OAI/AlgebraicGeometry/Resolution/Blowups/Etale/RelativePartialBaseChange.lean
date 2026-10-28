import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ModuleDerivations

/-! # Relative Partial Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativePartialBaseChange.Construction

noncomputable section

/-! Exact compatibility of coordinate partial derivatives with an étale refinement. -/

variable {σ K S T : Type*} [Field K] [CommRing S] [CommRing T] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]
  [Algebra K S] [IsScalarTower K (MvPolynomial σ K) S]
  [Algebra S T] [Algebra.FormallyEtale S T]
  [Algebra (MvPolynomial σ K) T] [Algebra.Etale (MvPolynomial σ K) T]
  [Algebra K T] [IsScalarTower K S T] [IsScalarTower K (MvPolynomial σ K) T]
  [IsScalarTower (MvPolynomial σ K) S T]

theorem etaleRelativePartial_extend (i : σ) :
    Derivation.Construction.extendEtaleRingDerivation (S := T) (DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) i) =
      DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := T) i := by
  apply ModuleDerivations.Construction.etale_relative_derivation_ext (σ := σ)
  intro j
  let E := Derivation.Construction.extendEtaleRingDerivation (S := T) (DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) i)
  calc
    E (algebraMap (MvPolynomial σ K) T (MvPolynomial.X j)) =
        E (algebraMap S T (algebraMap (MvPolynomial σ K) S (MvPolynomial.X j))) :=
      congrArg E (IsScalarTower.algebraMap_apply (MvPolynomial σ K) S T (MvPolynomial.X j))
    _ = algebraMap S T (DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) i
        (algebraMap (MvPolynomial σ K) S (MvPolynomial.X j))) :=
      Derivation.Construction.extendEtaleRingDerivation_algebraMap _ _
    _ = if i = j then 1 else 0 := by rw [TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X]; split_ifs <;> simp
    _ = DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := T) i
        (algebraMap (MvPolynomial σ K) T (MvPolynomial.X j)) := (TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X i j).symm

/-- The same intrinsic partial derivative acts on the image of every
original section after the étale refinement. -/
theorem etaleRelativePartial_baseChange (i : σ) (p : S) :
    DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := T) i (algebraMap S T p) =
      algebraMap S T (DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) i p) := by
  rw [← etaleRelativePartial_extend (S := S) i]
  exact Derivation.Construction.extendEtaleRingDerivation_algebraMap _ p

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativePartialBaseChange.Construction
