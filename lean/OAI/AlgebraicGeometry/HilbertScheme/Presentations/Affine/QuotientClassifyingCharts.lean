import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.QuotientMatrices
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ChartClassifyingMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints

/-! # Quotient Classifying Charts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.QuotientClassifyingCharts.Grassmannian

noncomputable section

/-!
Principal affine charts of an actual quotient module give compatible maps
into the constructed Grassmannian. Compatibility holds on every test
scheme over the coefficient ring.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable (R : CommRingCat.{u})

structure PrincipalQuotientChart (N : Module.Grassmannian R (ν → R) (Fintype.card ι)) where
  denominator : R
  columns : ι → ν
  matrix : Matrix ι ν (Localization.Away denominator)
  normalized : Normalized.Matrices.Grassmannian.IsNormalized columns matrix
  kernel : (Matrix.toLin' matrix).ker =
    Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R (Localization.Away denominator)) N.toSubmodule

def principalQuotientChartAt (N : Module.Grassmannian R (ν → R) (Fintype.card ι))
    (p : PrimeSpectrum R) : {D : PrincipalQuotientChart R N // D.denominator ∉ p.asIdeal} := by
  apply Classical.choice
  obtain ⟨r, a, Q, hr, _ha, hQ, hker⟩ := Principal.QuotientMatrices.Grassmannian.quotient_principal_normalized_matrix N p
  exact ⟨⟨⟨r, a, Q, hQ, hker⟩, hr⟩⟩

variable {R} {N : Module.Grassmannian R (ν → R) (Fintype.card ι)}

def PrincipalQuotientChart.scheme (D : PrincipalQuotientChart R N) : Over (Spec R) :=
  Relative.AffinePoints.relativeAffineScheme R (Localization.Away D.denominator)

def PrincipalQuotientChart.pointMatrix (D : PrincipalQuotientChart R N) {T : Over (Spec R)}
    (f : T ⟶ D.scheme) : Matrix ι ν Γ(T.left, ⊤) :=
  D.matrix.map (Relative.AffinePoints.relativeAffinePointEquiv R (Localization.Away D.denominator) T f).toRingHom

theorem PrincipalQuotientChart.pointMatrix_normalized (D : PrincipalQuotientChart R N)
    {T : Over (Spec R)} (f : T ⟶ D.scheme) : Normalized.Matrices.Grassmannian.IsNormalized D.columns (D.pointMatrix f) :=
  D.normalized.map (Relative.AffinePoints.relativeAffinePointEquiv R (Localization.Away D.denominator) T f).toRingHom

theorem PrincipalQuotientChart.pointMatrix_kernel (D : PrincipalQuotientChart R N)
    {T : Over (Spec R)} (f : T ⟶ D.scheme) :
    (Matrix.toLin' (D.pointMatrix f)).ker =
      Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R (Relative.AffinePoints.relativeGlobalAlgebra R T)) N.toSubmodule := by
  let φ := Relative.AffinePoints.relativeAffinePointEquiv R (Localization.Away D.denominator) T f
  change (Matrix.toLin' (D.matrix.map φ.toRingHom)).ker = _
  rw [← Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange φ.toRingHom D.columns D.matrix D.normalized,
    D.kernel, ← Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_comp]
  have hc : φ.toRingHom.comp (algebraMap R (Localization.Away D.denominator)) =
      algebraMap R (Relative.AffinePoints.relativeGlobalAlgebra R T) := by
    ext r
    exact φ.commutes r
  exact congrArg (fun α => Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension α N.toSubmodule) hc

theorem PrincipalQuotientChart.pointMatrix_comp (D : PrincipalQuotientChart R N)
    {T U : Over (Spec R)} (f : T ⟶ U) (g : U ⟶ D.scheme) :
    D.pointMatrix (f ≫ g) = (D.pointMatrix g).map f.left.appTop.hom := by
  exact congrArg
    (fun φ : Localization.Away D.denominator →ₐ[R] Relative.AffinePoints.relativeGlobalAlgebra R T => D.matrix.map φ.toRingHom)
    (Relative.AffinePoints.relativeAffinePointEquiv_natural R (Localization.Away D.denominator) f g)

def PrincipalQuotientChart.classifyingMap (D : PrincipalQuotientChart R N) :
    D.scheme ⟶ Presentations.Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := ν) (Spec R) :=
  Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap D.columns (D.pointMatrix (𝟙 _)) (D.pointMatrix_normalized (𝟙 _))

theorem PrincipalQuotientChart.classifyingMap_comp (D : PrincipalQuotientChart R N)
    {T : Over (Spec R)} (f : T ⟶ D.scheme) :
    f ≫ D.classifyingMap =
      Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap D.columns (D.pointMatrix f) (D.pointMatrix_normalized f) := by
  rw [PrincipalQuotientChart.classifyingMap, ← Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap_natural]
  have hm := D.pointMatrix_comp f (𝟙 _)
  rw [Category.comp_id] at hm
  congr 1

theorem PrincipalQuotientChart.classifyingMaps_agree (D E : PrincipalQuotientChart R N)
    {T : Over (Spec R)} (f : T ⟶ D.scheme) (g : T ⟶ E.scheme) :
    f ≫ D.classifyingMap = g ≫ E.classifyingMap := by
  rw [D.classifyingMap_comp, E.classifyingMap_comp, Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap_eq_iff,
    D.pointMatrix_kernel, E.pointMatrix_kernel]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.QuotientClassifyingCharts.Grassmannian
