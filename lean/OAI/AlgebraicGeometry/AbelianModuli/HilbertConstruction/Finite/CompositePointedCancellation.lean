import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsMapRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Composite Pointed Cancellation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CompositePointedCancellation

noncomputable section

/-! A finite map detects pointed maps out of a group family whose global
functions come from an affine base. No reducedness or Noetherian condition
on that base is required. -/
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} [IsAffine S]
variable {X Y Z : Over S} [MonObj X] [GrpObj Y] [GrpObj Z]
variable [IsIso X.hom.appTop]
variable (r : Y ⟶ Z) [IsFinite r.left]

theorem pointed_map_eq_one_of_finite_composite (a : X ⟶ Y)
    (ha : a ≫ r = 1) (hzero : η[X] ≫ a = η[Y]) : a = 1 := by
  have hw : a.left ≫ r.left = X.hom ≫ η[Z].left := congrArg Over.Hom.left ha
  let : IsAffine (𝟙_ (Over S)).left := inferInstanceAs (IsAffine S)
  let k : X.left ⟶ pullback r.left η[Z].left := pullback.lift a.left X.hom hw
  let : IsAffine (pullback r.left η[Z].left) :=
    isAffine_of_isAffineHom (pullback.snd r.left η[Z].left)
  have hk : k ≫ pullback.fst r.left η[Z].left = a.left := pullback.lift_fst _ _ _
  have hc := Global.FunctionsMapRigidity.affineMap_eq_of_globalFunctions_iso X.hom η[X].left η[X].w k
  have he : a.left = X.hom ≫ η[X].left ≫ a.left := by
    have hh := congrArg (fun u => u ≫ pullback.fst r.left η[Z].left) hc
    simpa only [Category.assoc, hk] using hh
  apply Over.OverMorphism.ext
  exact he.trans (congrArg (fun u => X.hom ≫ u) (congrArg Over.Hom.left hzero))

theorem pointed_maps_eq_of_finite_composite [IsMonHom r]
    (f q : X ⟶ Y) (hf : η[X] ≫ f = η[Y]) (hq : η[X] ≫ q = η[Y])
    (he : f ≫ r = q ≫ r) : f = q := by
  have hd : (f / q) ≫ r = 1 := by
    rw [GrpObj.div_comp, he, div_self']
  have hz : η[X] ≫ (f / q) = η[Y] := by
    rw [GrpObj.comp_div, hf, hq, div_self']
    simp only [MonObj.one_eq_one]
  exact div_eq_one.mp (pointed_map_eq_one_of_finite_composite r (f / q) hd hz)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CompositePointedCancellation
