import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Topology.KrullDimension

/-! # Local Dimension -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.LocalDimension.DimensionSupport

noncomputable section

/-! The local dimension argument from the proved Openness group-dimension
construction, using only actual translations and no statement-only imports. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem closed_point_translations
    {K : Type} [Field K] [IsAlgClosed K]
    (A : Over (Spec (.of K))) [GrpObj A] [LocallyOfFiniteType A.hom]
    (x y : A.left) (hx : IsClosed {x}) (hy : IsClosed {y}) :
    ∃ e : A.left ≅ A.left, e.hom x = y := by
  let x' : 𝟙_ (Over (Spec (.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom x hx) (pointOfClosedPoint_comp A.hom x hx)
  let y' : 𝟙_ (Over (Spec (.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom y hy) (pointOfClosedPoint_comp A.hom y hy)
  let b := x'⁻¹ * y'
  let e := (Over.forget (Spec (.of K))).mapIso (GrpObj.mulRight b)
  have hxy : x' ≫ (GrpObj.mulRight b).hom = y' := by
    change x' ≫ (𝟙 A * (toUnit A ≫ b)) = y'
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      comp_toUnit, toUnit_unit, Category.id_comp]
    exact mul_inv_cancel_left x' y'
  refine ⟨e, ?_⟩
  have he : e.hom (x'.left (IsLocalRing.closedPoint K)) = y'.left (IsLocalRing.closedPoint K) :=
    congrArg (fun f : Spec (.of K) ⟶ A.left => f (IsLocalRing.closedPoint K))
      (congrArg Over.Hom.left hxy)
  have hx' : x'.left (IsLocalRing.closedPoint K) = x := pointOfClosedPoint_apply A.hom x hx _
  have hy' : y'.left (IsLocalRing.closedPoint K) = y := pointOfClosedPoint_apply A.hom y hy _
  rw [hx', hy'] at he
  exact he

theorem topologicalKrullDim_eq_specialization_krullDim (X : Scheme) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

theorem topologicalKrullDim_eq_stalk_of_transitive_closedPoints
    (X : Scheme) [JacobsonSpace X]
    (htrans : ∀ (x y : X), IsClosed {x} → IsClosed {y} →
      ∃ e : X ≅ X, e.hom x = y)
    (x : X) (hx : IsClosed {x}) :
    topologicalKrullDim X = ringKrullDim (X.presheaf.stalk x) := by
  rw [ringKrullDim_stalk_eq_coheight, topologicalKrullDim_eq_specialization_krullDim]
  apply le_antisymm
  · rw [Order.krullDim_eq_iSup_coheight]
    apply iSup_le
    intro z
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints
      (Z := closure ({z} : Set X)) (Set.singleton_nonempty z).closure
      isClosed_closure.isLocallyClosed
    have hyz : y ≤ z := Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hy)
    obtain ⟨e, he⟩ := htrans y x hyc hx
    have hd : Order.coheight y = Order.coheight x := by
      rw [← he]
      exact (coheight_eq_of_isOpenImmersion e.hom).symm
    exact WithBot.coe_le_coe.mpr ((Order.coheight_anti hyz).trans_eq hd)
  · exact Order.coheight_le_krullDim x

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.LocalDimension.DimensionSupport
