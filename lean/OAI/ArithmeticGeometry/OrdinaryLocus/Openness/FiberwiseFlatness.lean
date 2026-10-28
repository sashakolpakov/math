import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LocalSchemeFlatness
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Fiberwise Flatness -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberwiseFlatness.Construction

noncomputable section

/-! The finite-morphism fiberwise flatness criterion for the Openness argument. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- A finite morphism of finite presentation between S-schemes is flat
if its source is S-flat and all its geometric base changes are flat. -/
theorem flat_finite_of_flat_geometric_baseChanges
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [IsFinite f.left] [LocallyOfFinitePresentation f.left] [Flat X.hom]
    (hfiber : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      Flat ((Over.pullback t).map f).left) : Flat f.left := by
  apply (RelativeBaseChange.Construction.flat_iff_flat_targetStalk_baseChange f.left).mpr
  intro y
  let s := Y.hom y
  let R : Type u := S.presheaf.stalk s
  let A : Type u := Y.left.presheaf.stalk y
  let instRA : Algebra R A := (Y.hom.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap R A) := Y.hom.toLRSHom.prop y
  let i := Y.left.fromSpecStalk y
  let q := pullback.snd f.left i
  let b := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have : Flat i := RelativeBaseChange.Construction.flat_fromSpecStalk Y.left y
  have heq : (q ≫ b) ≫ S.fromSpecStalk s = pullback.fst f.left i ≫ X.hom := by
    change (pullback.snd f.left i ≫ Spec.map (Y.hom.stalkMap y)) ≫
      S.fromSpecStalk s = _
    rw [Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, ← pullback.condition, Category.assoc, f.w]
  have : Flat ((q ≫ b) ≫ S.fromSpecStalk s) := by
    rw [heq]
    infer_instance
  have : Flat (q ≫ b) := RelativeBaseChange.Construction.flat_of_comp_fromSpecStalk s (q ≫ b)
  let k := ResidueField R
  let C := A ⊗[R] k
  let K := AlgebraicClosure k
  let D := C ⊗[k] K
  have : Module.FaithfullyFlat k K := inferInstance
  have : Module.FaithfullyFlat C D := inferInstance
  let j := Spec.map (CommRingCat.ofHom (algebraMap A D))
  let v := Spec.map (CommRingCat.ofHom (algebraMap K D))
  let rK := (algebraMap k K).comp (algebraMap R k)
  let t := Spec.map (CommRingCat.ofHom rK) ≫ S.fromSpecStalk s
  have hcomm : (j ≫ i) ≫ Y.hom = v ≫ t := by
    rw [Category.assoc]
    change j ≫ (Y.left.fromSpecStalk y ≫ Y.hom) = _
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc]
    have hc : j ≫ Spec.map (Y.hom.stalkMap y) =
        v ≫ Spec.map (CommRingCat.ofHom rK) := by
      dsimp [j, v]
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext r
      change (algebraMap A D) (algebraMap R A r) =
        (algebraMap K D) (algebraMap k K (algebraMap R k r))
      simp only [← IsScalarTower.algebraMap_apply R A D,
        ← IsScalarTower.algebraMap_apply k K D, ← IsScalarTower.algebraMap_apply R k D]
    rw [hc, Category.assoc]
  have : Flat ((Over.pullback t).map f).left := hfiber K t
  have : Flat (pullback.snd f.left (j ≫ i)) :=
    RelativeBaseChange.Construction.flat_targetBaseChange_of_factorization f t (j ≫ i) v hcomm
  have : Flat (pullback.snd q j) := RelativeBaseChange.Construction.flat_iterated_targetBaseChange f.left i j
  change Flat q
  exact @LocalSchemeFlatness.Construction.flat_finite_over_local_of_flat_closedFiber_baseChange R A D _ _ _ instRA
    _ _ _ _ _ _ _ _ q _ _ _ _

/-- The same criterion when flatness is supplied over every field. -/
theorem flat_finite_of_flat_field_baseChanges
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [IsFinite f.left] [LocallyOfFinitePresentation f.left] [Flat X.hom]
    (hfiber : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ S),
      Flat ((Over.pullback t).map f).left) : Flat f.left :=
  flat_finite_of_flat_geometric_baseChanges f (fun K _ _ t => hfiber K t)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberwiseFlatness.Construction
