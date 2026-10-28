import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-! # Cocycle Bilinear Descent -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.CocycleBilinearDescent.Cycles

noncomputable section

/-!
# Bilinear operations on actual cohomology from cocycle operations

This is quotient algebra for genuine cochain complexes. A bilinear pairing
of their actual cocycles descends when its two boundary images are proved
to be actual coboundaries. Relative cup products apply this construction
to the explicit front/back cochain product.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

variable {R : Type} [CommRing R]
  (C D E : CochainComplex (ModuleCat.{0} R) ℕ) (p q n : ℕ)
  (B : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles C p →ₗ[R] AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles D q →ₗ[R] AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles E n)
  (hleft : ∀ (b : (C.sc p).X₁) (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles D q),
    B (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaryMap C p b) d ∈ AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries E n)
  (hright : ∀ (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles C p) (b : (D.sc q).X₁),
    B c (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaryMap D q b) ∈ AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries E n)

/-- Descend a proved cocycle pairing through the actual two coboundary
quotients and mathlib's canonical cohomology identifications. -/
def cohomologyBilinearOfCocycles : C.homology p →ₗ[R] D.homology q →ₗ[R] E.homology n :=
  (((B.compr₂ (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass E n)).liftQ₂
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries C p) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries D q)
    (by
      rintro c ⟨b, rfl⟩
      apply LinearMap.ext
      intro d
      exact (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_zero_iff E n _).mpr (hleft b d))
    (by
      rintro d ⟨b, rfl⟩
      apply LinearMap.ext
      intro c
      exact (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_zero_iff E n _).mpr (hright c b))).comp
    (AlgebraicTopology.Cohomology.Singular.Representatives.cohomologyQuotientIso C p).toLinearEquiv.toLinearMap).compl₂
      (AlgebraicTopology.Cohomology.Singular.Representatives.cohomologyQuotientIso D q).toLinearEquiv.toLinearMap

/-- The descended operation is represented by the specified actual
cocycle pairing, for every pair of representatives. -/
@[simp]
theorem cohomologyBilinearOfCocycles_class_class
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles C p) (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles D q) :
    cohomologyBilinearOfCocycles C D E p q n B hleft hright
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass C p c) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass D q d) = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass E n (B c d) := by
  simp only [cohomologyBilinearOfCocycles, AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass, LinearMap.compl₂_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- Compatibility of the actual cocycle operations with three cochain
maps implies compatibility of the descended operations on cohomology. -/
theorem cohomologyBilinearOfCocycles_naturality
    (C' D' E' : CochainComplex (ModuleCat.{0} R) ℕ)
    (B' : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles C' p →ₗ[R] AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles D' q →ₗ[R] AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles E' n)
    (hleft' : ∀ (b : (C'.sc p).X₁) (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles D' q),
      B' (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaryMap C' p b) d ∈ AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries E' n)
    (hright' : ∀ (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles C' p) (b : (D'.sc q).X₁),
      B' c (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaryMap D' q b) ∈ AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries E' n)
    (f : C ⟶ C') (g : D ⟶ D') (h : E ⟶ E')
    (hB : ∀ c d, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap h n (B c d) =
      B' (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap f p c) (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap g q d))
    (x : C.homology p) (y : D.homology q) :
    HomologicalComplex.homologyMap h n
        (cohomologyBilinearOfCocycles C D E p q n B hleft hright x y) =
      cohomologyBilinearOfCocycles C' D' E' p q n B' hleft' hright'
        (HomologicalComplex.homologyMap f p x) (HomologicalComplex.homologyMap g q y) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective C p x
  obtain ⟨d, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective D q y
  simp only [cohomologyBilinearOfCocycles_class_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  exact congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass E' n) (hB c d)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.CocycleBilinearDescent.Cycles
