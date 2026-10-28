import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ConfigurationEvaluation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoordinateBasis

/-! # Monomial Matrix -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.MonomialMatrix

noncomputable section

/-! Polynomial configuration evaluation has a fixed monomial matrix
whose index set is independent of the coefficient ring. Its entries
are literal monomial values and commute with every coefficient map. -/
open scoped BigOperators
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert
universe u v
variable {R : Type u} [CommRing R] {n d : ℕ}
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

def configurationMonomialMatrix (w : ι → Fin (n + 1) → R) (d : ℕ) :
    Matrix ι (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n d) R :=
  Homogeneous.ConfigurationEvaluation.homogeneousConfigurationMatrix (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n d) w

theorem configurationMonomialMatrix_entry (w : ι → Fin (n + 1) → R)
    (c : ι) (a : HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n d) :
    configurationMonomialMatrix w d c a = a.down.val.prod (fun j k => w c j ^ k) := by
  change MvPolynomial.eval₂Hom (algebraMap R R) (w c) ((HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n d) a).val = _
  rw [HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis_val, MvPolynomial.eval₂Hom_monomial, map_one, one_mul]

theorem configurationMonomialMatrix_map {A : Type u} [CommRing A] (φ : R →+* A)
    (w : ι → Fin (n + 1) → R) :
    (configurationMonomialMatrix w d).map φ = configurationMonomialMatrix (fun c j => φ (w c j)) d := by
  ext c a
  change φ (configurationMonomialMatrix w d c a) = configurationMonomialMatrix (fun c j => φ (w c j)) d c a
  rw [configurationMonomialMatrix_entry, configurationMonomialMatrix_entry]
  simp only [Finsupp.prod, map_prod, map_pow]

theorem configurationMonomialMatrix_range (w : ι → Fin (n + 1) → R) :
    (Matrix.toLin' (configurationMonomialMatrix w d)).range = (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w d).range := by
  rw [show configurationMonomialMatrix w d = Homogeneous.ConfigurationEvaluation.homogeneousConfigurationMatrix (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n d) w from rfl,
    Homogeneous.ConfigurationEvaluation.homogeneousConfigurationMatrix_linearMap]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n d).equivFun.symm x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n d).equivFun.symm.surjective x
    exact ⟨z, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.MonomialMatrix
