import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricTorsionPoints

/-! # Finite Rational Points -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteRationalPoints.Construction

noncomputable section

/-! Finite rational point sets and finite schemes over algebraically closed fields. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def rationalPointsClosedEquiv
    {K : Type u} [Field K] [IsAlgClosed K]
    (T : Over (Spec (.of K))) [LocallyOfFiniteType T.hom] :
    (Over.mk (𝟙 (Spec (.of K))) ⟶ T) ≃ closedPoints T.left := by
  let e : (Over.mk (𝟙 (Spec (.of K))) ⟶ T) ≃
      {f : Spec (.of K) ⟶ T.left // f ≫ T.hom = 𝟙 _} :=
    { toFun := fun f => ⟨f.left, f.w⟩
      invFun := fun f => Over.homMk f.val f.property
      left_inv := fun f => by apply Over.OverMorphism.ext; rfl
      right_inv := fun f => rfl }
  exact e.trans (pointEquivClosedPoint T.hom)

/-- Finitely many rational points force a finite underlying space over an
algebraically closed field for a locally finite-type scheme. -/
theorem finite_scheme_of_finite_rationalPoints
    {K : Type u} [Field K] [IsAlgClosed K]
    (T : Over (Spec (.of K))) [LocallyOfFiniteType T.hom]
    [Finite (Over.mk (𝟙 (Spec (.of K))) ⟶ T)] : Finite T.left := by
  have : Finite (closedPoints T.left) := Finite.of_equiv _ (rationalPointsClosedEquiv T)
  have : JacobsonSpace T.left := LocallyOfFiniteType.jacobsonSpace T.hom
  have hfin : (closedPoints T.left).Finite := Set.toFinite _
  have : DiscreteTopology T.left := JacobsonSpace.discreteTopology hfin
  apply Set.finite_univ_iff.mp
  simpa only [closedPoints_eq_univ] using hfin

/-- Properness upgrades a finite rational point set to a finite structural morphism. -/
theorem isFinite_of_proper_of_finite_rationalPoints
    {K : Type u} [Field K] [IsAlgClosed K]
    (T : Over (Spec (.of K))) [IsProper T.hom]
    [Finite (Over.mk (𝟙 (Spec (.of K))) ⟶ T)] : IsFinite T.hom := by
  have : Finite T.left := finite_scheme_of_finite_rationalPoints T
  have : LocallyQuasiFinite T.hom :=
    LocallyQuasiFinite.of_finite_preimage_singleton T.hom (fun _ => Set.toFinite _)
  exact (IsFinite.iff_isProper_and_locallyQuasiFinite T.hom).mpr ⟨inferInstance, inferInstance⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteRationalPoints.Construction
