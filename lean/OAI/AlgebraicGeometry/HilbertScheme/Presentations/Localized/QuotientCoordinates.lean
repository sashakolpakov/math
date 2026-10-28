import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.KernelBaseChange
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-! # Quotient Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.QuotientCoordinates.Grassmannian

noncomputable section

/-! Coordinate presentations of localized quotient modules and their exact kernels. -/

open _root_.Module LocalizedModule

universe u

variable {R M ν : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable [Fintype ν] [DecidableEq ν] (p : Submonoid R)

abbrev coordinateLocalization : (ν → R) →ₗ[R] (ν → Localization p) :=
  LinearMap.pi (fun i => (Algebra.linearMap R (Localization p)).comp (LinearMap.proj i))

omit [Fintype ν] in
theorem coordinateLocalization_single (i : ν) :
    coordinateLocalization (ν := ν) p (Pi.single i 1) = Pi.single i 1 := by
  ext j
  simp [coordinateLocalization, Pi.single_apply]

def localizedCoordinateMap (q : (ν → R) →ₗ[R] M) :
    (ν → Localization p) →ₗ[Localization p] LocalizedModule p M :=
  (IsLocalizedModule.map p (coordinateLocalization p) (LocalizedModule.mkLinearMap p M) q).extendScalarsOfIsLocalization
    p (Localization p)

omit [DecidableEq ν] in
theorem localizedCoordinateMap_apply (q : (ν → R) →ₗ[R] M) (x : ν → R) :
    localizedCoordinateMap p q (coordinateLocalization p x) = LocalizedModule.mkLinearMap p M (q x) :=
  IsLocalizedModule.map_apply p (coordinateLocalization p) (LocalizedModule.mkLinearMap p M) q x

theorem localizedCoordinateMap_single (q : (ν → R) →ₗ[R] M) (i : ν) :
    localizedCoordinateMap p q (Pi.single i 1) = LocalizedModule.mkLinearMap p M (q (Pi.single i 1)) := by
  rw [← coordinateLocalization_single p i]
  exact localizedCoordinateMap_apply p q _

omit [DecidableEq ν] in
theorem localizedCoordinateMap_kernel (q : (ν → R) →ₗ[R] M) :
    (localizedCoordinateMap p q).ker =
      Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R (Localization p)) q.ker := by
  exact (LinearMap.localized'_ker_eq_ker_localizedMap (Localization p) p
    (coordinateLocalization p) (LocalizedModule.mkLinearMap p M) q).symm.trans
      (Submodule.localized'_eq_span _ _ _ _)

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

def localizedBasisMatrix (q : (ν → R) →ₗ[R] M)
    (B : Basis ι (Localization p) (LocalizedModule p M)) : Matrix ι ν (Localization p) :=
  LinearMap.toMatrix' (B.equivFun.toLinearMap.comp (localizedCoordinateMap p q))

theorem localizedBasisMatrix_normalized (q : (ν → R) →ₗ[R] M)
    (a : ι → ν) (B : Basis ι (Localization p) (LocalizedModule p M))
    (hB : ∀ i, B i = LocalizedModule.mkLinearMap p M (q (Pi.single (a i) 1))) :
    Normalized.Matrices.Grassmannian.IsNormalized a (localizedBasisMatrix p q B) := by
  ext i j
  change LinearMap.toMatrix' (B.equivFun.toLinearMap.comp (localizedCoordinateMap p q)) i (a j) = _
  rw [LinearMap.toMatrix'_apply, LinearMap.comp_apply, localizedCoordinateMap_single, ← hB j]
  simp [Matrix.one_apply, eq_comm]

omit [DecidableEq ι] in
theorem localizedBasisMatrix_kernel (q : (ν → R) →ₗ[R] M)
    (B : Basis ι (Localization p) (LocalizedModule p M)) :
    (Matrix.toLin' (localizedBasisMatrix p q B)).ker =
      Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R (Localization p)) q.ker := by
  rw [localizedBasisMatrix, Matrix.toLin'_toMatrix', LinearEquiv.ker_comp,
    localizedCoordinateMap_kernel]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.QuotientCoordinates.Grassmannian
