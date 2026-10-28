import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SingleHomologyShift
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.TensorSingle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CocycleHomology
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.CochainShift

/-! # Column Homology -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ColumnHomology

noncomputable section

/-! Flat tensor-column homology, normalized by the native single-functor
shift laws, with compatibility for degree-changing cocycles. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CochainComplex.HomComplex

variable (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℤ)

def singles : SingleFunctors (ModuleCat.{0} R) (CochainComplex (ModuleCat.{0} R) ℤ) ℤ :=
  (CochainComplex.singleFunctors (ModuleCat.{0} R)).postcomp (Homotopy.complexFunctor R K)

def iso (M : ModuleCat.{0} R) [Module.Flat R M] (d n k : ℤ) (h : -d + n = k) :
    ((Homotopy.complexFunctor R K).obj
      ((CochainComplex.singleFunctor (ModuleCat.{0} R) d).obj M)).homology n ≅
        (tensorLeft M).obj (K.homology k) :=
  SingleHomologyShift.iso (singles R K)
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) 0) M d n k h ≪≫
    TensorSingle.Naturality.flatHomologyIso R K M k

@[reassoc]
theorem naturality {M N : ModuleCat.{0} R} [Module.Flat R M] [Module.Flat R N]
    (f : M ⟶ N) (d n k : ℤ) (h : -d + n = k) :
    HomologicalComplex.homologyMap ((Homotopy.complexFunctor R K).map
      ((CochainComplex.singleFunctor (ModuleCat.{0} R) d).map f)) n ≫ (iso R K N d n k h).hom =
      (iso R K M d n k h).hom ≫ ((curriedTensor (ModuleCat.{0} R)).map f).app (K.homology k) := by
  simp only [iso, Iso.trans_hom]
  change ((HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) 0).shift n).map
    (((singles R K).functor d).map f) ≫ _ = _
  rw [← Category.assoc, SingleHomologyShift.naturality]
  simp only [Category.assoc]
  congr 1
  exact TensorSingle.Naturality.flatHomologyIso_naturality R K f k

theorem tensor_shifted_map {M N : ModuleCat.{0} R} (a d e : ℤ) (he : a + d = e)
    (z : Cocycle ((CochainComplex.singleFunctor (ModuleCat.{0} R) d).obj M)
      ((CochainComplex.singleFunctor (ModuleCat.{0} R) e).obj N) a) (f : M ⟶ N)
    (hz : Cocycle.equivHomShift.symm z ≫
      ((CochainComplex.singleFunctors (ModuleCat.{0} R)).shiftIso a d e he).hom.app N =
        (CochainComplex.singleFunctor (ModuleCat.{0} R) d).map f) :
    Cocycle.equivHomShift.symm (Cochain.mapCocycle R K z) ≫
      ((singles R K).shiftIso a d e he).hom.app N =
        (Homotopy.complexFunctor R K).map
          ((CochainComplex.singleFunctor (ModuleCat.{0} R) d).map f) := by
  change Cocycle.equivHomShift.symm (Cochain.mapCocycle R K z) ≫
    (((CochainComplex.singleFunctors (ModuleCat.{0} R)).postcomp
      (Homotopy.complexFunctor R K)).shiftIso a d e he).hom.app N = _
  rw [SingleFunctors.postcomp_shiftIso_hom_app, Cocycle.equivHomShift_symm_apply,
    ← CochainShift.homOf_rightShift]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (Homotopy.complexFunctor R K).map hz

@[reassoc]
theorem shifted_naturality {M N : ModuleCat.{0} R} [Module.Flat R M] [Module.Flat R N]
    (a d e n m k : ℤ) (he : a + d = e) (hm : a + n = m) (hk : -d + n = k)
    (z : Cocycle ((CochainComplex.singleFunctor (ModuleCat.{0} R) d).obj M)
      ((CochainComplex.singleFunctor (ModuleCat.{0} R) e).obj N) a) (f : M ⟶ N)
    (hz : Cocycle.equivHomShift.symm z ≫
      ((CochainComplex.singleFunctors (ModuleCat.{0} R)).shiftIso a d e he).hom.app N =
        (CochainComplex.singleFunctor (ModuleCat.{0} R) d).map f) :
    CocycleHomology.map R (Cochain.mapCocycle R K z) n m hm ≫
        (iso R K N e m k (by omega)).hom =
      (iso R K M d n k hk).hom ≫ ((curriedTensor (ModuleCat.{0} R)).map f).app (K.homology k) := by
  simp only [iso, Iso.trans_hom]
  rw [← Category.assoc]
  change ((HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) 0).shiftMap
      (Cocycle.equivHomShift.symm (Cochain.mapCocycle R K z)) n m hm ≫
    (SingleHomologyShift.iso (singles R K)
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) 0) N e m k (by omega)).hom) ≫ _ = _
  rw [SingleHomologyShift.shiftMap (singles R K) _ N a d e n m k he hm hk,
    tensor_shifted_map R K a d e he z f hz]
  change (HomologicalComplex.homologyMap ((Homotopy.complexFunctor R K).map
      ((CochainComplex.singleFunctor (ModuleCat.{0} R) d).map f)) n ≫ _) ≫ _ = _
  rw [Category.assoc]
  exact naturality R K f d n k hk

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ColumnHomology
