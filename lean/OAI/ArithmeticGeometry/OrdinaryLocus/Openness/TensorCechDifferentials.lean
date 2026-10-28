import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CechBaseChangeCoordinates

/-! # Tensor Cech Differentials -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorCechDifferentials.Construction

noncomputable section

/-! Tensoring the actual Cech differentials commutes with finite-product coordinates. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped TensorProduct

universe u

variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    {X : TopCat.{u}} (F : TopCat.Sheaf (ModuleCat.{u} R) X)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → Opens X)

def tensorCechD0 : CechBaseChangeCoordinates.Construction.tensorCechC0 (K := K) F U →ₗ[K] CechBaseChangeCoordinates.Construction.tensorCechC1 (K := K) F U where
  toFun z i j := (F.obj.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op).hom.baseChange K (z j) -
    (F.obj.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op).hom.baseChange K (z i)
  map_add' x y := by funext i j; simp only [Pi.add_apply, map_add, sub_add_sub_comm]
  map_smul' r x := by funext i j; simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply]

def tensorCechRestrict1 (z : CechBaseChangeCoordinates.Construction.tensorCechC1 (K := K) F U) (i j : ι) (W : Opens X)
    (hi : W ≤ U i) (hj : W ≤ U j) : K ⊗[R] F.obj.obj (op W) :=
  (F.obj.map (homOfLE (le_inf hi hj)).op).hom.baseChange K (z i j)

def tensorCechD1 : CechBaseChangeCoordinates.Construction.tensorCechC1 (K := K) F U →ₗ[K] CechBaseChangeCoordinates.Construction.tensorCechC2 (K := K) F U where
  toFun z i j k :=
    tensorCechRestrict1 F U z i j ((U i ⊓ U j) ⊓ U k)
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) +
    tensorCechRestrict1 F U z j k ((U i ⊓ U j) ⊓ U k)
      (inf_le_left.trans inf_le_right) inf_le_right -
    tensorCechRestrict1 F U z i k ((U i ⊓ U j) ⊓ U k)
      (inf_le_left.trans inf_le_left) inf_le_right
  map_add' x y := by
    funext i j k
    simp only [tensorCechRestrict1, Pi.add_apply, map_add]
    abel
  map_smul' r x := by
    funext i j k
    simp only [tensorCechRestrict1, Pi.smul_apply, map_smul, smul_add, smul_sub, RingHom.id_apply]

theorem cechBaseChangeCoordinates_d0 :
    (CechBaseChangeCoordinates.Construction.cechBaseChangeCoordinates1 (K := K) F U).toLinearMap.comp ((OpenCechDegreeZero.Construction.openModuleCechD0 F U).baseChange K) =
      (tensorCechD0 F U).comp (CechBaseChangeCoordinates.Construction.cechBaseChangeCoordinates0 F U).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a z
  funext i j
  change a ⊗ₜ[R] (OpenCechDegreeZero.Construction.openModuleCechD0 F U z i j) =
    a ⊗ₜ[R] F.obj.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op (z j) -
      a ⊗ₜ[R] F.obj.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op (z i)
  exact TensorProduct.tmul_sub _ _ _

theorem cechBaseChangeCoordinates_d1 :
    (CechBaseChangeCoordinates.Construction.cechBaseChangeCoordinates2 (K := K) F U).toLinearMap.comp ((OpenCechShortComplex.Construction.openModuleCechD1 F U).baseChange K) =
      (tensorCechD1 F U).comp (CechBaseChangeCoordinates.Construction.cechBaseChangeCoordinates1 F U).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a z
  funext i j k
  change a ⊗ₜ[R]
      (OpenCechCocycles.Construction.openCechRestrict1 F U z i j _ (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) +
        OpenCechCocycles.Construction.openCechRestrict1 F U z j k _ (inf_le_left.trans inf_le_right) inf_le_right -
        OpenCechCocycles.Construction.openCechRestrict1 F U z i k _ (inf_le_left.trans inf_le_left) inf_le_right) =
    a ⊗ₜ[R] OpenCechCocycles.Construction.openCechRestrict1 F U z i j _ (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) +
      a ⊗ₜ[R] OpenCechCocycles.Construction.openCechRestrict1 F U z j k _ (inf_le_left.trans inf_le_right) inf_le_right -
      a ⊗ₜ[R] OpenCechCocycles.Construction.openCechRestrict1 F U z i k _ (inf_le_left.trans inf_le_left) inf_le_right
  rw [TensorProduct.tmul_sub, TensorProduct.tmul_add]

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorCechDifferentials.Construction
