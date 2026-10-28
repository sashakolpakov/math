import OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericZeroLift
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PointClosureLocalTest
import OAI.RepresentationTheory.Theta.Geometric.SpecLocalRings

/-! # Relative Specialization -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeSpecialization.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! Over a proper parameter family, the image of the original Picard
zero scheme is stable under specialization. Actual integral point
closures and their local stalks provide the extending test maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.RepresentationTheory.Theta.Geometric.SpecLocalRings

variable {S : Scheme} {A B : Over S} [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [IsLocallyNoetherian B.left] (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A)
    (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)
    {Y : Scheme} (p : B.left ⟶ Y) [IsProper p]

theorem zeroProjection_range_stableUnderSpecialization :
    StableUnderSpecialization (Set.range ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom ≫ p)) := by
  intro y y' hyy
  rintro ⟨z, rfl⟩
  let x := (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z
  let C := PointClosureLocalTest.Geometric.pointClosure x
  let i := PointClosureLocalTest.Geometric.pointClosureInclusion x
  let : IsIntegral C := PointClosureLocalTest.Geometric.pointClosure_integral x
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian i
  let : IsProper (i ≫ p) := inferInstance
  have hc : IsClosed (Set.range (i ≫ p)) := (i ≫ p).isClosedMap.isClosed_range
  have hx : p x ∈ Set.range (i ≫ p) := by
    refine ⟨genericPoint C, ?_⟩
    change p (i (genericPoint C)) = p x
    exact congrArg p (PointClosureLocalTest.Geometric.pointClosure_generic x)
  obtain ⟨c, hc⟩ := hyy.mem_closed hc hx
  let R := C.presheaf.stalk c
  let u : Spec R ⟶ B.left := C.fromSpecStalk c ≫ i
  let V : Over S := Over.mk (u ≫ B.hom)
  let a : V ⟶ B := Over.homMk u rfl
  let : IsAffine V.left := inferInstanceAs (IsAffine (Spec R))
  let : IsIntegral V.left := inferInstanceAs (IsIntegral (Spec R))
  let : IsLocallyNoetherian V.left := inferInstanceAs (IsLocallyNoetherian (Spec R))
  let : IsLocalRing Γ(V.left, ⊤) := RepresentationTheory.Theta.Geometric.SpecLocalRings.specGlobal_isLocalRing R
  let : IsNoetherianRing Γ(V.left, ⊤) := RepresentationTheory.Theta.Geometric.SpecLocalRings.specGlobal_isNoetherianRing R
  have hη : a.left (genericPoint V.left) = (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z := by
    change i (C.fromSpecStalk c (genericPoint (Spec R))) = x
    rw [PointClosureLocalTest.Geometric.integral_fromSpecStalk_generic]
    exact PointClosureLocalTest.Geometric.pointClosure_generic x
  obtain ⟨w, hw⟩ := GenericZeroLift.Geometric.RelativeRigidifiedCharts.zeroScheme_generic_lift P D a z hη
  refine ⟨w.left (IsLocalRing.closedPoint R), ?_⟩
  have he := congrArg (fun f : V ⟶ B => p (f.left (IsLocalRing.closedPoint R))) hw
  apply he.trans
  change p (i (C.fromSpecStalk c (IsLocalRing.closedPoint R))) = y'
  rw [Scheme.fromSpecStalk_closedPoint]
  exact hc

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeSpecialization.Geometric.RelativeRigidifiedCharts
