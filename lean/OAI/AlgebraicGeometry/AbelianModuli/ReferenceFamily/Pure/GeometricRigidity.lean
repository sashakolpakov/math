import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.ComplexRigidity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.AutomorphismDescent
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricFieldModel

/-! # Geometric Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.GeometricRigidity

noncomputable section

/-! Full-level rigidity on every geometric fiber of a pure family over
a finite-type characteristic-zero parameter. Countable fields of
definition and proved endomorphism descent handle geometric fields of
arbitrary cardinality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricFieldModel

variable {K : Type} [Field K] [CharZero K] [Countable K]
    {X : Scheme.{0}} (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N X)

include p in
theorem pureGeometricPullback_abelian_eq_id (hN : 3 ≤ N)
    {k : Type} [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback x) (A.pullback x)) :
    e.abelian.hom = 𝟙 (A.abelian.pullback x).scheme := by
  obtain ⟨M⟩ := AbelianScheme.TateComparison.GeometricFieldModel.geometricPoint_has_countable_model K p x
  let bk := Spec.map (CommRingCat.ofHom M.toOriginal)
  let bc : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of M.field) := Spec.map (CommRingCat.ofHom M.toComplex)
  let xc := bc ≫ M.point
  have hcomplex : ∀ j : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback xc) (A.pullback xc),
      j.abelian.hom = 𝟙 (A.pullback xc).abelian.scheme := by
    intro j
    exact ComplexRigidity.pureComplex_abelian_eq_id (A.pullback xc) j hN
  exact AutomorphismDescent.pure_abelian_eq_id_of_common_model bk bc
    (A.pullback M.point) (A.pullback x) (A.pullback xc)
    (AutomorphismDescent.purePullbackFactor A bk M.point x M.factor)
    (AutomorphismDescent.purePullbackFactor A bc M.point xc rfl) hcomplex e

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.GeometricRigidity
