import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasis

/-! # Trace Basis Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasisRestriction

noncomputable section

/-! Genuine finite étale trace charts remain valid on affine subopens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasis
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTraceRestriction

universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left]

omit [Etale (Over.Hom.left f)] in
theorem good (U V : Y.left.Opens) (hU : TraceBasis.Good R X Y f U)
    (hV : IsAffineOpen V) (hVU : V ≤ U) : TraceBasis.Good R X Y f V := by
  let a : TraceBasis.Index R X Y f := ⟨U, hU⟩
  let : Fact (IsAffineOpen U) := ⟨hU.1⟩
  let : Fact (IsAffineOpen V) := ⟨hV⟩
  let : Fact (V ≤ U) := ⟨hVU⟩
  let := AffineOpen.DeRhamTrace.sectionAlgebra R X Y f U
  let := AffineOpen.DeRhamTrace.sectionAlgebra R X Y f V
  let : Module.Free (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) := hU.2.2
  let := AffineOpen.DeRhamTraceRestriction.targetAlgebra R Y U V
  let := AffineOpen.DeRhamTraceRestriction.sourceAlgebra R X Y f U V
  let := AffineOpen.DeRhamTraceRestriction.diagonalAlgebra R X Y f U V
  let := AffineOpen.DeRhamTraceRestriction.firstDiagonalTower R X Y f U V
  let := AffineOpen.DeRhamTraceRestriction.secondDiagonalTower R X Y f U V
  let := AffineOpen.DeRhamTraceRestriction.sectionPushout R X Y f U V
  have hfree : FreeNeighborhood.IsFreeOn R X Y f V :=
    Module.Free.of_equiv (Algebra.IsPushout.equiv (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.targetRing R Y V)
      (AffineOpen.DeRhamTrace.sourceRing R X Y f U) (AffineOpen.DeRhamTrace.sourceRing R X Y f V)).toLinearEquiv
  let σ := TraceBasis.coordinateIndex R X Y f a
  let : LinearOrder σ := TraceBasis.coordinateOrder R X Y f a
  let : Algebra (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U) := TraceBasis.polynomialAlgebra R X Y f a
  let : IsScalarTower R (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U) := TraceBasis.coordinateTower R X Y f a
  let : Algebra.Etale (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U) := TraceBasis.coordinateEtale R X Y f a
  let : Algebra (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y V) :=
    ((algebraMap (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.targetRing R Y V)).comp
      (algebraMap (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U))).toAlgebra
  let : IsScalarTower (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.targetRing R Y V) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y V) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      change algebraMap R (AffineOpen.DeRhamTrace.targetRing R Y V) r =
        algebraMap (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.targetRing R Y V)
          (algebraMap (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U) (algebraMap R (MvPolynomial σ R) r))
      rw [← IsScalarTower.algebraMap_apply R (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U)]
      exact (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y).map (AffineOpen.DeRhamTraceRestriction.targetInclusion R Y U V).op).hom.commutes r).symm)
  exact ⟨hV, ⟨σ, inferInstance, inferInstance, inferInstance,
    AffineOpen.DeRhamTraceRestriction.smallerEtale R Y U V σ⟩, hfree⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasisRestriction
