import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Branches

/-! # Scalars -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Scalars

noncomputable section

/-! The zero-parameter local ring and its integral closure retain the
given ground-field scalars. The parameter is an actual integral element. -/

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Place OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveParameter OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Branches

variable (k L : Type) [Field k] [Field L] [Algebra k L]
  (g : L) (hg : Transcendental k g)

theorem scalarTower :
    letI := Branches.localAlgebra k L g hg
    IsScalarTower k (ProjectionFormula.Polynomial.Place.localRing k) L := by
  let := CurveParameter.polynomialAlgebra k L g
  let := CurveParameter.fractionAlgebra k L g hg
  let := Branches.localAlgebra k L g hg
  let := Branches.localTower k L g hg
  let : IsScalarTower k (Polynomial k) L := IsScalarTower.of_algHom (Polynomial.aeval g)
  let : FaithfulSMul (Polynomial k) L :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial k) L).mpr (CurveParameter.polynomialAlgebra_injective k L g hg)
  let : IsScalarTower (Polynomial k) (FractionRing (Polynomial k)) L :=
    FractionRing.isScalarTower_liftAlgebra (Polynomial k) L
  let : IsScalarTower k (FractionRing (Polynomial k)) L :=
    IsScalarTower.to₁₃₄ k (Polynomial k) (FractionRing (Polynomial k)) L
  let : IsScalarTower k (ProjectionFormula.Polynomial.Place.localRing k) (FractionRing (Polynomial k)) :=
    IsScalarTower.to₁₃₄ k (Polynomial k) (ProjectionFormula.Polynomial.Place.localRing k) (FractionRing (Polynomial k))
  apply IsScalarTower.of_algebraMap_eq
  intro c
  rw [IsScalarTower.algebraMap_apply (ProjectionFormula.Polynomial.Place.localRing k) (FractionRing (Polynomial k)) L,
    ← IsScalarTower.algebraMap_apply k (ProjectionFormula.Polynomial.Place.localRing k) (FractionRing (Polynomial k)),
    ← IsScalarTower.algebraMap_apply]

abbrev closureScalarAlgebra :
    letI := Branches.localAlgebra k L g hg
    Algebra k (integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L) :=
  letI := Branches.localAlgebra k L g hg
  ((algebraMap (ProjectionFormula.Polynomial.Place.localRing k) (integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L)).comp
    (algebraMap k (ProjectionFormula.Polynomial.Place.localRing k))).toAlgebra

theorem closureScalarTower :
    letI := Branches.localAlgebra k L g hg
    letI := closureScalarAlgebra k L g hg
    IsScalarTower k (integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L) L := by
  let := Branches.localAlgebra k L g hg
  let := closureScalarAlgebra k L g hg
  let := scalarTower k L g hg
  let : IsScalarTower k (ProjectionFormula.Polynomial.Place.localRing k) (integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact IsScalarTower.to₁₃₄ k (ProjectionFormula.Polynomial.Place.localRing k) (integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L) L

theorem parameter_integer :
    letI := Branches.localAlgebra k L g hg
    ∃ a : integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L, algebraMap (integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L) L a = g := by
  let := CurveParameter.polynomialAlgebra k L g
  let := CurveParameter.fractionAlgebra k L g hg
  let := Branches.localAlgebra k L g hg
  let := Branches.localTower k L g hg
  refine ⟨algebraMap (ProjectionFormula.Polynomial.Place.localRing k) (integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L)
    (algebraMap (Polynomial k) (ProjectionFormula.Polynomial.Place.localRing k) Polynomial.X), ?_⟩
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (ProjectionFormula.Polynomial.Place.localRing k) (FractionRing (Polynomial k)) L,
    ← IsScalarTower.algebraMap_apply (Polynomial k) (ProjectionFormula.Polynomial.Place.localRing k) (FractionRing (Polynomial k))]
  exact CurveParameter.parameter_image k L g hg

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Scalars
