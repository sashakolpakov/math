import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DiagonalFrame
import OAI.RepresentationTheory.Weil.AdelicSplitting.Assembly

/-! # Global Frames -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.GlobalFrames.CM

noncomputable section

/-! ThetaCycle: the diagonal rational frame and all its actual local realizations. -/

open scoped Classical
open OAI.RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction

variable (F : Type) [Field F] [NumberField F] {n m : ℕ}

theorem localized_diagonal_hermitian (d : F)
    (h : Fin n → F) (hh : ∀ j, h j ≠ 0) (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d (DiagonalFrame.CM.diagonalHermitianUnit d h hh) v).val =
      DiagonalFrame.CM.diagonalUnitaryHermitian (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) (fun j => RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v (h j)) := by
  change (DiagonalFrame.CM.diagonalUnitaryHermitian d h).map (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v) = _
  unfold DiagonalFrame.CM.diagonalUnitaryHermitian
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1
  funext j
  apply QuadraticAlgebra.ext <;>
    simp [RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal, RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange]

theorem localized_diagonal_skew (d : F) (hd : d ≠ 0)
    (a : Fin m → F) (ha : ∀ i, a i ≠ 0) (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d (DiagonalFrame.CM.diagonalSkewUnit d hd a ha) v).val =
      DiagonalFrame.CM.diagonalUnitarySkew (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) (fun i => RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v (a i)) := by
  change (DiagonalFrame.CM.diagonalUnitarySkew d a).map (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v) = _
  unfold DiagonalFrame.CM.diagonalUnitarySkew
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  apply QuadraticAlgebra.ext <;>
    simp [RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal, RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange, map_ofNat]

/-- These are the native AdelicSplitting frames, with compatibility proved on rational
vectors. Every local frame uses the same real/imaginary coordinate formula. -/
def diagonalGlobalFrames (d : F) (hd : d ≠ 0)
    (h : Fin n → F) (hh : ∀ j, h j ≠ 0) (a : Fin m → F) (ha : ∀ i, a i ≠ 0) :
    RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m (DiagonalFrame.CM.diagonalHermitianUnit d h hh) (DiagonalFrame.CM.diagonalSkewUnit d hd a ha) where
  rational := DiagonalFrame.CM.diagonalUnitaryFrame d hd h hh a ha
  localFrame v := {
    coordinates := (DiagonalFrame.CM.diagonalUnitaryFrame (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d)
      ((map_ne_zero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v)).mpr hd)
      (fun j => RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v (h j))
      (fun j => (map_ne_zero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v)).mpr (hh j))
      (fun i => RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v (a i))
      (fun i => (map_ne_zero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v)).mpr (ha i))).coordinates
    preserves := by
      rw [localized_diagonal_hermitian, localized_diagonal_skew]
      exact (DiagonalFrame.CM.diagonalUnitaryFrame (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d)
        ((map_ne_zero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v)).mpr hd)
        (fun j => RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v (h j))
        (fun j => (map_ne_zero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v)).mpr (hh j))
        (fun i => RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v (a i))
        (fun i => (map_ne_zero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v)).mpr (ha i))).preserves }
  coordinates_compatible v x i :=
    DiagonalFrame.CM.diagonal_frame_baseChange (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v) d hd h hh a ha x i

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.GlobalFrames.CM
