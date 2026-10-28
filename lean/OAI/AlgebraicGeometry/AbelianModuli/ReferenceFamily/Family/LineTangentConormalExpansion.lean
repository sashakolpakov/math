import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.LineIntrinsicClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.RegularCocycle

/-! # Line Tangent Conormal Expansion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.LineTangentConormalExpansion

noncomputable section

/-! The actual line-bundle tangent constraint is the finite sum of
the original tangent-cocycle coordinates multiplied by the original
constant-direction line logarithms, on literal triple intersections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct BigOperators

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)]

attribute [local implicit_reducible] AffineCoverIntersections.familyCoverAffineOpen AffineCoverIntersections.familyCoverPairAffineOpen AffineCoverIntersections.familyCoverTripleAffineOpen
attribute [local implicit_reducible] Fixed.CechCover.fixedFamilyCechCover TangentBasePoint.fixedFamilyFiber FixedFiber.CoordinateProjection.fixedFiberAffineOpen
attribute [local irreducible] FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv FixedFiber.ConstantDerivations.fixedFiberConormalCoefficientEquiv
attribute [local irreducible] FixedFiber.RegularSections.fixedFiberRegularSectionEquiv

omit [IsSeparated X.hom] in
theorem familyCommonOpenConormal_restrict {V W Z Q : X.left.affineOpens}
    (t : V.1 ≤ W.1) (h : W.1 ≤ Z.1) (j : W.1 ≤ Q.1) (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) :
    FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X V (CommonOpenTangentDifferences.familyCommonOpenTangentDifference ℂ R X (t.trans h) (t.trans j) d) z =
      FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X t
        (FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X W (CommonOpenTangentDifferences.familyCommonOpenTangentDifference ℂ R X h j d) z) := by
  have hd := LinearMap.congr_fun (FamilyTangent.DifferenceNaturality.familyCommonOpenTangentDifference_restrict ℂ R X t h j) d
  change FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R ℂ X t (CommonOpenTangentDifferences.familyCommonOpenTangentDifference ℂ R X h j d) =
    CommonOpenTangentDifferences.familyCommonOpenTangentDifference ℂ R X (t.trans h) (t.trans j) d at hd
  rw [← hd, FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv_natural]

variable (U : X.left.AffineOpenCover)
    (D : HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions (fun i => (AffineCoverIntersections.familyCoverAffineOpen R X U i).1))
    {I : Type} [Fintype I] (b : Module.Basis I ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)))

theorem familyLineTangentTriple_conormalExpansion (d : Derivation ℂ R ℂ) (i j l : U.I₀) :
    LineTangentBoundary.familyLineTangentTriple ℂ R X U D d i j l = ∑ a,
      FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X
        (show (AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 from inf_le_left)
        (FamilyTangent.ConormalCocycle.familyTangentConormalPair R X U i j d (b a)) *
      FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X
        (show (AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (AffineCoverIntersections.familyCoverPairAffineOpen R X U j l).1 from
          le_inf (inf_le_left.trans inf_le_right) inf_le_right) (FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogPair R X U D (b.coord a) j l) := by
  let V := AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l
  let B := ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V
  let hi : V.1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U i).1 := inf_le_left.trans inf_le_left
  let hj : V.1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U j).1 := inf_le_left.trans inf_le_right
  let hl : V.1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U l).1 := inf_le_right
  let u := FixedFiber.LineLogCocycle.fixedFiberFrameReducedUnit R ℂ X _ D V j l hj hl
  let q := CommonOpenTangentDifferences.familyCommonOpenTangentDifference ℂ R X hi hj d
  calc
    _ = ∑ a, FixedFiber.ConstantDerivations.fixedFiberConormalCoefficientEquiv R X V q (b a) *
        ConormalUnitLogCoordinates.conormalUnitLogCoordinate B b (FixedFiber.ConstantDerivations.fixedFiberConormalCoefficientEquiv R X V) u a :=
      ConormalUnitLogCoordinates.coefficientUnitLog_conormal_expansion B b (FixedFiber.ConstantDerivations.fixedFiberConormalCoefficientEquiv R X V) u q
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply congrArg₂ (· * ·)
      · change (FixedFiber.ConstantDerivations.fixedFiberConormalCoefficientEquiv R X V).restrictScalars ℂ q (b a) = _
        rw [FixedFiber.ConstantDerivations.fixedFiberConormalCoefficientEquiv_restrictScalars]
        exact familyCommonOpenConormal_restrict R X
          (show V.1 ≤ (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 from inf_le_left)
          (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U i).1 from inf_le_left)
          (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U j).1 from inf_le_right) d (b a)
      · exact FixedFiber.LineLogCocycle.fixedFiberLineLogCoefficient_restrict R X _ D (b.coord a)
          (show V.1 ≤ (AffineCoverIntersections.familyCoverPairAffineOpen R X U j l).1 from le_inf hj hl)
          j l inf_le_left inf_le_right

theorem familyLineTangentRegularTriple_conormalExpansion (d : Derivation ℂ R ℂ) (i j l : U.I₀) :
    LineIntrinsicClass.familyLineTangentRegularTriple ℂ R X U D d i j l = ∑ a,
      (TangentBasePoint.fixedFamilyFiber ℂ R X).left.presheaf.map
        (homOfLE (show (Fixed.CechCover.fixedFamilyCechCover ℂ R X U i ⊓ Fixed.CechCover.fixedFamilyCechCover ℂ R X U j) ⊓
          Fixed.CechCover.fixedFamilyCechCover ℂ R X U l ≤ Fixed.CechCover.fixedFamilyCechCover ℂ R X U i ⊓ Fixed.CechCover.fixedFamilyCechCover ℂ R X U j from
          inf_le_left)).op (FamilyTangent.RegularCocycle.familyTangentRegularPair R X U d (b a) i j) *
      (TangentBasePoint.fixedFamilyFiber ℂ R X).left.presheaf.map
        (homOfLE (show (Fixed.CechCover.fixedFamilyCechCover ℂ R X U i ⊓ Fixed.CechCover.fixedFamilyCechCover ℂ R X U j) ⊓
          Fixed.CechCover.fixedFamilyCechCover ℂ R X U l ≤ Fixed.CechCover.fixedFamilyCechCover ℂ R X U j ⊓ Fixed.CechCover.fixedFamilyCechCover ℂ R X U l from
          le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op (FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogRegularPair R X U D (b.coord a) j l) := by
  have h := congrArg (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X (AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l))
    (familyLineTangentTriple_conormalExpansion R X U D b d i j l)
  rw [map_sum] at h
  simp only [map_mul, FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_restrict] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.LineTangentConormalExpansion
