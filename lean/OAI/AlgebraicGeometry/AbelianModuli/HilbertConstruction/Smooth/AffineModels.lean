import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ModelCartesian
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Affine Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineModels

noncomputable section

/-! Smooth affine algebras admit actual smooth flat scheme models over noetherian coefficient rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

structure SmoothAffineModel where
  coefficients : Subalgebra ℤ R
  finiteType : Algebra.FiniteType ℤ coefficients
  algebra : CommAlgCat.{u} coefficients
  smooth : Algebra.Smooth coefficients algebra
  recovery : A ≃ₐ[R] R ⊗[coefficients] algebra

attribute [instance] SmoothAffineModel.finiteType SmoothAffineModel.smooth

theorem smoothAffineModel_nonempty [Algebra.Smooth R A] : Nonempty (SmoothAffineModel R A) := by
  obtain ⟨C, B, _, _, hC, hB, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ R A
  exact ⟨{
    coefficients := C
    finiteType := (Subalgebra.fg_iff_finiteType C).mp hC
    algebra := CommAlgCat.of C B
    smooth := hB
    recovery := e }⟩

namespace SmoothAffineModel

variable {R A} (M : SmoothAffineModel R A)

instance coefficients_noetherian : IsNoetherianRing M.coefficients :=
  Algebra.FiniteType.isNoetherianRing ℤ M.coefficients

instance algebra_noetherian : IsNoetherianRing M.algebra :=
  Algebra.FiniteType.isNoetherianRing M.coefficients M.algebra

def structureMap : Spec (.of M.algebra) ⟶ Spec (.of M.coefficients) :=
  Spec.map (CommRingCat.ofHom (algebraMap M.coefficients M.algebra))

instance structureMap_smooth : Smooth M.structureMap := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.smooth_algebraMap.mpr M.smooth

instance structureMap_flat : Flat M.structureMap := inferInstance

def map : Spec (.of A) ⟶ Spec (.of M.algebra) := Tensor.ModelCartesian.tensorModelMap M.recovery

theorem isPullback :
    IsPullback M.map (Spec.map (CommRingCat.ofHom (algebraMap R A))) M.structureMap
      (Spec.map (CommRingCat.ofHom M.coefficients.val.toRingHom)) :=
  Tensor.ModelCartesian.tensorModelMap_isPullback M.recovery

end SmoothAffineModel

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineModels
