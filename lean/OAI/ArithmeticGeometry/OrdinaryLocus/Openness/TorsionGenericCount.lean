import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ClosedGeometricPoint
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat

/-! # Torsion Generic Count -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TorsionGenericCount.Construction

noncomputable section

/-! Comparing rational torsion points with the generic multiplication fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj

/-- The torsion scheme is the base change of multiplication along the unit. -/
def torsionIdentityFiberIso
    {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    DefinitionsTorsion.Construction.torsionScheme A n ≅
      (Over.pullback η[A].left).obj (Over.mk (Multiplication.Construction.multiplicationMap A n).left) := by
  let h := FinitePresentation.Construction.torsion_isPullback A n
  let h' := IsPullback.of_hasPullback (Multiplication.Construction.multiplicationMap A n).left η[A].left
  exact Over.isoMk (h.isoIsPullback _ _ h') (h.isoIsPullback_hom_snd _ _ h')

theorem torsionPointCard_eq_identityFiberCard
    {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    Nat.card {x : Over.mk (𝟙 S) ⟶ A // x ^ n = 1} =
      Nat.card (Over.mk η[A].left ⟶ Over.mk (Multiplication.Construction.multiplicationMap A n).left) := by
  let P : Over S := Over.mk (𝟙 S)
  let T : Over A.left := Over.mk (Multiplication.Construction.multiplicationMap A n).left
  let e₀ : (Over.map η[A].left).obj P ≅ Over.mk η[A].left :=
    Over.isoMk (Iso.refl _) (by simp [P])
  let e := (DefinitionsTorsion.Construction.torsionPointsEquiv A n P).symm.trans
    ((Iso.homCongr (Iso.refl P) (torsionIdentityFiberIso A n)).trans
      (((Over.mapPullbackAdj η[A].left).homEquiv P T).symm.trans
        (Iso.homCongr e₀ (Iso.refl T))))
  exact Nat.card_congr e

/-- For the natural abelian fibers in Openness, the rational torsion count is
bounded by the generic geometric fiber count of multiplication. -/
theorem torsionPointCard_le_generic_multiplication
    {K : Type*} [Field K] [IsAlgClosed K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (n : ℕ) [IsFinite (DefinitionsTorsion.Construction.torsionScheme A n).hom] :
    letI : IsIntegral A.left := ConnectedGroupIntegral.Construction.isIntegral_connected_smooth_proper_group A
    Nat.card {x : Over.mk (𝟙 (Spec (.of K))) ⟶ A // x ^ n = 1} ≤
      Nat.card (DefinitionsTorsion.geometricPoint A.left (genericPoint A.left) ⟶
        Over.mk (Multiplication.Construction.multiplicationMap A n).left) := by
  have : IsIntegral A.left := ConnectedGroupIntegral.Construction.isIntegral_connected_smooth_proper_group A
  have : IsFinite (Multiplication.Construction.multiplicationMap A n).left :=
    Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion A n
  have : Flat (Multiplication.Construction.multiplicationMap A n).left :=
    FieldMultiplicationFlat.Construction.flat_multiplication_of_isFinite_torsion_over_algClosed A n
  have : LocallyOfFinitePresentation (Multiplication.Construction.multiplicationMap A n).left :=
    FinitePresentation.Construction.locallyOfFinitePresentation_multiplication A n
  let x : A.left := η[A].left (IsLocalRing.closedPoint K)
  have hx : IsClosed {x} := by
    exact (pointEquivClosedPoint A.hom ⟨η[A].left, by simp⟩).property
  have hp : pointOfClosedPoint A.hom x hx = η[A].left :=
    ext_of_apply_closedPoint_eq A.hom (pointOfClosedPoint_comp A.hom x hx)
      (by simp) (pointOfClosedPoint_apply A.hom x hx _)
  have hc := ClosedGeometricPoint.Construction.geometricPointCard_closed A.hom
    (Over.mk (Multiplication.Construction.multiplicationMap A n).left) x hx
  rw [hp] at hc
  rw [torsionPointCard_eq_identityFiberCard, ← hc]
  exact @GenericPointCount.Construction.geometricPointCard_le_generic A.left inferInstance
    (Over.mk (Multiplication.Construction.multiplicationMap A n).left)
    ‹IsFinite (Multiplication.Construction.multiplicationMap A n).left› ‹Flat (Multiplication.Construction.multiplicationMap A n).left›
    ‹LocallyOfFinitePresentation (Multiplication.Construction.multiplicationMap A n).left› x

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TorsionGenericCount.Construction
