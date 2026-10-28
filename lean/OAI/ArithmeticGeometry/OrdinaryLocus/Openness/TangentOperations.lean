import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PointedTangentAt

/-! # Tangent Operations -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TangentOperations.Construction.PointedTangent

/-!
# Openness: linearizing a unital operation on pointed schemes

The hypotheses are identities of actual scheme morphisms: the two unit
insertions project as expected and multiplying either insertion is the
identity. The additive formula is proved from the tangent functor.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {C : CommRingCat.{u}} [IsLocalRing C]
variable (J : Ideal C) (hJ : J ^ 2 = ⊥)

theorem map_comp_apply {P Q R : Under (Spec C)} (f : P ⟶ Q) (g : Q ⟶ R)
    (v : PointedTangentAt.Construction.PointedTangent.Space J hJ P.hom) : PointedTangentAt.Construction.PointedTangent.map J hJ g (PointedTangentAt.Construction.PointedTangent.map J hJ f v) = PointedTangentAt.Construction.PointedTangent.map J hJ (f ≫ g) v := by
  rw [PointedTangentAt.Construction.PointedTangent.map_comp, LinearMap.comp_apply]

/-- A unital scheme operation sends the sum of the two inserted relative
tangents to their sum, and the constructed point has the required projections. -/
theorem exists_product_point
    {P R K : Under (Spec C)} (f : P ⟶ R) (e : R ⟶ P)
    (p q m : K ⟶ P) (i j : P ⟶ K)
    (hip : i ≫ p = 𝟙 P) (hiq : i ≫ q = f ≫ e)
    (hjp : j ≫ p = f ≫ e) (hjq : j ≫ q = 𝟙 P)
    (him : i ≫ m = 𝟙 P) (hjm : j ≫ m = 𝟙 P)
    (v w : PointedTangentAt.Construction.PointedTangent.Space J hJ P.hom) (hv : PointedTangentAt.Construction.PointedTangent.map J hJ f v = 0) (hw : PointedTangentAt.Construction.PointedTangent.map J hJ f w = 0) :
    ∃ z : Spec C ⟶ K.right,
      z ≫ p.right = PointedTangentAt.Construction.PointedTangent.point J hJ P.hom v ∧
      z ≫ q.right = PointedTangentAt.Construction.PointedTangent.point J hJ P.hom w ∧
      z ≫ m.right = PointedTangentAt.Construction.PointedTangent.point J hJ P.hom (v + w) := by
  let t := PointedTangentAt.Construction.PointedTangent.map J hJ i v + PointedTangentAt.Construction.PointedTangent.map J hJ j w
  have hp : PointedTangentAt.Construction.PointedTangent.map J hJ p t = v := by
    simp only [t, map_add, map_comp_apply, hip, hjp, PointedTangentAt.Construction.PointedTangent.map_comp, LinearMap.comp_apply,
      PointedTangentAt.Construction.PointedTangent.map_id, LinearMap.id_apply, hw, map_zero, add_zero]
  have hq : PointedTangentAt.Construction.PointedTangent.map J hJ q t = w := by
    simp only [t, map_add, map_comp_apply, hiq, hjq, PointedTangentAt.Construction.PointedTangent.map_comp, LinearMap.comp_apply,
      PointedTangentAt.Construction.PointedTangent.map_id, LinearMap.id_apply, hv, map_zero, zero_add]
  have hm : PointedTangentAt.Construction.PointedTangent.map J hJ m t = v + w := by
    simp only [t, map_add, map_comp_apply, him, hjm, PointedTangentAt.Construction.PointedTangent.map_id, LinearMap.id_apply]
  refine ⟨PointedTangentAt.Construction.PointedTangent.point J hJ K.hom t, ?_, ?_, ?_⟩
  · exact (PointedTangentAt.Construction.PointedTangent.point_map J hJ p t).symm.trans (congrArg (PointedTangentAt.Construction.PointedTangent.point J hJ P.hom) hp)
  · exact (PointedTangentAt.Construction.PointedTangent.point_map J hJ q t).symm.trans (congrArg (PointedTangentAt.Construction.PointedTangent.point J hJ P.hom) hq)
  · exact (PointedTangentAt.Construction.PointedTangent.point_map J hJ m t).symm.trans (congrArg (PointedTangentAt.Construction.PointedTangent.point J hJ P.hom) hm)

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TangentOperations.Construction.PointedTangent
