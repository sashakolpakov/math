import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SchemePoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantPointMap

/-! # Point Retraction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PointRetraction.CM

noncomputable section

/-! A finite scheme over an algebraically closed field maps canonically
to the constant scheme of its rational points. The original rational
points give a section, while the fibers retain their nilpotent structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (T : Over (Spec (.of k))) [IsFinite T.hom]

def labels : LocallyConstant T.left (Over.mk (𝟙 (Spec (.of k))) ⟶ T) := by
  let : DiscreteTopology T.left := SchemePoints.CM.discreteTopology T
  exact ⟨(SchemePoints.CM.pointsEquiv T).symm,
    IsLocallyConstant.of_discrete _⟩

theorem labels_point (p : Over.mk (𝟙 (Spec (.of k))) ⟶ T) :
    labels T (SchemePoints.CM.pointsEquiv T p) = p :=
  (SchemePoints.CM.pointsEquiv T).symm_apply_apply p

def retraction : T ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ T) :=
  AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointInverse T (labels T)

theorem retraction_points (p : Over.mk (𝟙 (Spec (.of k))) ⟶ T) :
    p ≫ retraction T =
      ConstantPointMap.CM.point (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ T) p := by
  apply (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ T)
    (Over.mk (𝟙 (Spec (.of k))))).injective
  apply LocallyConstant.ext
  intro z
  change AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T (retraction T) (p.left z) =
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ T)
      (Sigma.ι (fun _ : Over.mk (𝟙 (Spec (.of k))) ⟶ T => Spec (.of k)) p z)
  calc
    _ = labels T (p.left z) :=
      congrArg (fun c : LocallyConstant T.left (Over.mk (𝟙 (Spec (.of k))) ⟶ T) => c (p.left z))
        (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint_rightInverse T (labels T))
    _ = labels T (SchemePoints.CM.pointsEquiv T p) :=
      congrArg (fun w => labels T (p.left w))
        (Subsingleton.elim (α := Spec (.of k)) z (IsLocalRing.closedPoint k))
    _ = p := labels_point T p
    _ = _ := (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι p z).symm

theorem hom_ext_to_constant (I : Type u)
    (f g : T ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I)
    (h : ∀ p : Over.mk (𝟙 (Spec (.of k))) ⟶ T, p ≫ f = p ≫ g) : f = g := by
  apply (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of k)) I T).injective
  apply LocallyConstant.ext
  intro t
  obtain ⟨p, rfl⟩ := (SchemePoints.CM.pointsEquiv T).surjective t
  exact congrArg (fun z : Over.mk (𝟙 (Spec (.of k))) ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I =>
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint (Over.mk (𝟙 (Spec (.of k)))) z (IsLocalRing.closedPoint k)) (h p)

theorem section_retraction :
    ConstantPointMap.CM.ofPoints (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ T) T id ≫
      retraction T = 𝟙 _ := by
  apply ConstantPointMap.CM.hom_ext (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ T)
    (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ T))
  intro p
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ retraction T)
      (ConstantPointMap.CM.point_ofPoints (Spec (.of k))
        (Over.mk (𝟙 (Spec (.of k))) ⟶ T) T id p)).trans
      ((retraction_points T p).trans (Category.comp_id _).symm))

def pointMap {U : Over (Spec (.of k))} (f : T ⟶ U) :
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ T) ⟶
      AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ U) :=
  ConstantPointMap.CM.ofPoints (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ T)
    (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ U))
    (fun p => ConstantPointMap.CM.point (Spec (.of k))
      (Over.mk (𝟙 (Spec (.of k))) ⟶ U) (p ≫ f))

theorem naturality (U : Over (Spec (.of k))) [IsFinite U.hom] (f : T ⟶ U) :
    f ≫ retraction U = retraction T ≫ pointMap T f := by
  apply hom_ext_to_constant T (Over.mk (𝟙 (Spec (.of k))) ⟶ U)
  intro p
  calc
    p ≫ f ≫ retraction U = (p ≫ f) ≫ retraction U := (Category.assoc _ _ _).symm
    _ = ConstantPointMap.CM.point (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ U) (p ≫ f) :=
      retraction_points U (p ≫ f)
    _ = ConstantPointMap.CM.point (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ T) p ≫
        pointMap T f :=
      (ConstantPointMap.CM.point_ofPoints (Spec (.of k))
        (Over.mk (𝟙 (Spec (.of k))) ⟶ T)
        (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ U))
        (fun p => ConstantPointMap.CM.point (Spec (.of k))
          (Over.mk (𝟙 (Spec (.of k))) ⟶ U) (p ≫ f)) p).symm
    _ = (p ≫ retraction T) ≫ pointMap T f :=
      congrArg (fun z => z ≫ pointMap T f) (retraction_points T p).symm
    _ = p ≫ retraction T ≫ pointMap T f := Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PointRetraction.CM
