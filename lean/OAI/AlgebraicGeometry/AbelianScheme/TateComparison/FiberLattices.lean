import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricLattice
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FlagComposites
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitBlocks

/-! # Fiber Lattices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiberLattices

noncomputable section

/-! Apply the geometric lattice construction to the actual TateComparison fibers
and composites. Characteristic zero is derived from the geometric point's
map to the number-field base. The split summands are finite free as well. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u

theorem charZero_of_field_spec_map {K k : Type u} [Field K] [CharZero K] [Field k]
    (b : Spec (.of k) ⟶ Spec (.of K)) : CharZero k := by
  let f : K →+* k := (Spec.preimage b).hom
  exact charZero_of_injective_ringHom f.injective

namespace SphericalPELAlbaneseData

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  {k : Type} [Field k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)

local instance : Module ℚ_[q]
    (Rational.rationalTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :=
  TensorProduct.leftModule

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.fiberTate_finite : Module.Finite ℤ_[q]
    (Add.schemeTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) := by
  have := charZero_of_field_spec_map b
  exact GeometricLattice.geometricTate_finite (D.fiberFamily b x).abelian q

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.fiberIntegralTateImage_isLattice : Submodule.IsLattice ℚ_[q]
    (Rational.integralTateImage (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) := by
  have := D.fiberTate_finite b x
  have : Module.Free ℤ_[q]
      (Add.schemeTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :=
    Module.free_of_finite_type_torsion_free' (R := ℤ_[q])
      (M := Add.schemeTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)
  exact TensorLattice.tensorIntegralImage_isLattice (Module.finBasis ℤ_[q]
    (Add.schemeTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q))

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.fiberTateBlock_finite_free (h : D.IsGoodCompletelySplitPrime) (v : Fin s × Bool) :
    Module.Finite ℤ_[q] (D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) v) ∧
    Module.Free ℤ_[q] (D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) v) := by
  have := D.fiberTate_finite b x
  have : Module.Finite ℤ_[q]
      (D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) v) := inferInstance
  have : Module.IsTorsionFree ℤ_[q]
      (D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) v) :=
    Module.IsTorsionFree.of_smul_eq_zero fun (r : ℤ_[q])
        (z : D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) v) hz => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · apply Or.inr
        apply Subtype.ext
        exact Functor.Tate.smul_eq_zero_of_ne_zero q r hr z.val (congrArg Subtype.val hz)
  exact ⟨inferInstance, Module.free_of_finite_type_torsion_free' (R := ℤ_[q])
    (M := D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) v)⟩

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.flagCompositeLattice_isLattice {ts : List (Local.IntegralType s)}
    (F : D.PELFlag b x ts) (p : D.CompositeSystem F) (e : D.FiberFrame b x)
    (j : Fin (ts.length + 1)) (v : Fin s × Bool) :
    Submodule.IsLattice ℚ_[q] (D.compositeLattice e p j v) := by
  have := D.fiberIntegralTateImage_isLattice b (F.point j)
  exact IsogenyLattices.framedTateLattice_isLattice
    (A := (D.fiberFamily b x).abelian) (B := (D.fiberFamily b (F.point j)).abelian)
    (𝟙 (Spec (.of k))) q e (p j).isogeny v

end SphericalPELAlbaneseData

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiberLattices
