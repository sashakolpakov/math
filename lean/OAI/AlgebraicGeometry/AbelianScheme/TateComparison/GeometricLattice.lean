import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteGeneration
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricDivision
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TensorLattice
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyLattices

/-! # Geometric Lattice -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricLattice

noncomputable section

/-! Actual geometric Tate modules are finite free, and their integral
images are full lattices. This uses finite multiplication kernels and
geometric division, over every algebraically closed characteristic-zero
field; no complex embedding or projective presentation is required. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u
variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (q : ℕ) [Fact q.Prime]

theorem geometric_torsion_finite (n : ℕ) :
    Finite (Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme)) n) := by
  let e := GeometricDivision.multiplicationIsogeny A (q ^ n)
  have : Finite (e.kernelAt (Over.mk (𝟙 (Spec (.of k))))) :=
    FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricKernel_finite e (𝟙 (Spec (.of k)))
  let f : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme)) n →
      e.kernelAt (Over.mk (𝟙 (Spec (.of k)))) := fun x =>
    ⟨x.val.toMul, by
      change x.val.toMul ≫ (𝟙 A.scheme) ^ (q ^ n) = 1
      rw [MonObj.comp_pow, Category.comp_id]
      exact congrArg Additive.toMul x.property⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  apply Additive.toMul.injective
  have he := congrArg (fun z : e.kernelAt (Over.mk (𝟙 (Spec (.of k)))) => z.val) h
  exact he

theorem geometricTate_finite :
    Module.Finite ℤ_[q] (Add.schemeTateModule A.scheme (Over.mk (𝟙 (Spec (.of k)))) q) := by
  have := geometric_torsion_finite A q 1
  exact FiniteGeneration.Tate.finite_of_finite_torsion q (GeometricDivision.geometricPoint_divisible A q)

theorem geometricTate_free :
    Module.Free ℤ_[q] (Add.schemeTateModule A.scheme (Over.mk (𝟙 (Spec (.of k)))) q) := by
  have := geometricTate_finite A q
  infer_instance

def geometricTateBasis :
    Module.Basis
      (Fin (Module.finrank ℤ_[q] (Add.schemeTateModule A.scheme (Over.mk (𝟙 (Spec (.of k)))) q)))
      ℤ_[q] (Add.schemeTateModule A.scheme (Over.mk (𝟙 (Spec (.of k)))) q) := by
  have := geometricTate_finite A q
  have := geometricTate_free A q
  exact Module.finBasis _ _

theorem geometricIntegralTateImage_isLattice :
    Submodule.IsLattice ℚ_[q] (Rational.integralTateImage A.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :=
  TensorLattice.tensorIntegralImage_isLattice (geometricTateBasis A q)

theorem geometricIsogenyTatePreimage_isLattice {h : ℕ}
    {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))} (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) :
    Submodule.IsLattice ℚ_[q]
      (Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.hom) := by
  have := geometricIntegralTateImage_isLattice B q
  exact IsogenyLattices.isogenyTatePreimage_isLattice (𝟙 (Spec (.of k))) q f

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricLattice
