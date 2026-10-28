import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Homotopy
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-! # Cochain -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Cochain

noncomputable section

/-! Tensoring arbitrary homogeneous cochains in the first factor. The
construction acts on the actual summands of the native total tensor complex. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CochainComplex.HomComplex

variable (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℤ)

local instance hasMapBifunctor (P Q : CochainComplex (ModuleCat.{0} R) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor (ModuleCat.{0} R)) (.up ℤ) := by
  intro n
  infer_instance

variable {P Q S : CochainComplex (ModuleCat.{0} R) ℤ} {a b : ℤ}

def map (z : Cochain P Q a) :
    Cochain ((Homotopy.complexFunctor R K).obj P)
      ((Homotopy.complexFunctor R K).obj Q) a :=
  Cochain.mk (fun n m hnm =>
    HomologicalComplex.mapBifunctorDesc (fun i j hij =>
      ((curriedTensor (ModuleCat.{0} R)).map (z.v i (i + a) rfl)).app (K.X j) ≫
        HomologicalComplex.ιMapBifunctor Q K (curriedTensor (ModuleCat.{0} R)) (.up ℤ)
          (i + a) j m (by change i + j = n at hij; change (i + a) + j = m; omega)))

@[reassoc]
theorem ι_map (z : Cochain P Q a) (n m i j : ℤ) (hnm : n + a = m) (hij : i + j = n) :
    HomologicalComplex.ιMapBifunctor P K (curriedTensor (ModuleCat.{0} R)) (.up ℤ) i j n hij ≫
        (Tensor.Cochain.map R K z).v n m hnm =
      ((curriedTensor (ModuleCat.{0} R)).map (z.v i (i + a) rfl)).app (K.X j) ≫
        HomologicalComplex.ιMapBifunctor Q K (curriedTensor (ModuleCat.{0} R)) (.up ℤ)
          (i + a) j m (by change (i + a) + j = m; omega) := by
  simp only [Tensor.Cochain.map, Cochain.mk_v, HomologicalComplex.ι_mapBifunctorDesc]

theorem map_zero : Tensor.Cochain.map R K (0 : Cochain P Q a) = 0 := by
  apply Cochain.ext
  intro n m hnm
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [ι_map R K _ n m i j hnm hij]
  simp only [Cochain.zero_v, Functor.map_zero, NatTrans.app_zero,
    CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]

theorem map_add (z w : Cochain P Q a) : Tensor.Cochain.map R K (z + w) = Tensor.Cochain.map R K z + Tensor.Cochain.map R K w := by
  apply Cochain.ext
  intro n m hnm
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  simp only [Cochain.add_v, Preadditive.comp_add, ι_map R K _ n m i j hnm hij,
    Functor.map_add, NatTrans.app_add, Preadditive.add_comp]

@[reassoc]
theorem ι_map_v (z : Cochain P Q a) (n m i j i' : ℤ)
    (hnm : n + a = m) (hij : i + j = n) (hi : i + a = i') :
    HomologicalComplex.ιMapBifunctor P K (curriedTensor (ModuleCat.{0} R)) (.up ℤ) i j n hij ≫
        (Tensor.Cochain.map R K z).v n m hnm =
      ((curriedTensor (ModuleCat.{0} R)).map (z.v i i' hi)).app (K.X j) ≫
        HomologicalComplex.ιMapBifunctor Q K (curriedTensor (ModuleCat.{0} R)) (.up ℤ)
          i' j m (by change i' + j = m; omega) := by
  subst i'
  exact ι_map R K z n m i j hnm hij

def additiveMap : Cochain P Q a →+ Cochain ((Homotopy.complexFunctor R K).obj P)
    ((Homotopy.complexFunctor R K).obj Q) a where
  toFun := Tensor.Cochain.map R K
  map_zero' := Tensor.Cochain.map_zero R K
  map_add' := Tensor.Cochain.map_add R K

theorem map_neg (z : Cochain P Q a) : Tensor.Cochain.map R K (-z) = -Tensor.Cochain.map R K z :=
  (additiveMap R K).map_neg z

theorem map_zsmul (r : ℤ) (z : Cochain P Q a) : Tensor.Cochain.map R K (r • z) = r • Tensor.Cochain.map R K z :=
  (additiveMap R K).map_zsmul r z

theorem map_comp (z : Cochain P Q a) (w : Cochain Q S b) {c : ℤ} (h : a + b = c) :
    Tensor.Cochain.map R K (z.comp w h) = (Tensor.Cochain.map R K z).comp (Tensor.Cochain.map R K w) h := by
  apply Cochain.ext
  intro n m hnm
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  rw [ι_map R K _ n m i j hnm hij,
    Cochain.comp_v z w h i (i + a) (i + c) rfl (by omega),
    Cochain.comp_v (Tensor.Cochain.map R K z) (Tensor.Cochain.map R K w) h n (n + a) m rfl (by omega),
    ι_map_assoc R K z n (n + a) i j rfl hij,
    ι_map_v R K w (n + a) m (i + a) j (i + c) (by omega) (by omega) (by omega)]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]

theorem map_ofHom (f : P ⟶ Q) :
    Tensor.Cochain.map R K (Cochain.ofHom f) = Cochain.ofHom ((Homotopy.complexFunctor R K).map f) := by
  apply Cochain.ext₀
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [ι_map_v R K (Cochain.ofHom f) n n i j i (add_zero n) hij (add_zero i)]
  change _ = HomologicalComplex.ιMapBifunctor P K (curriedTensor (ModuleCat.{0} R)) (.up ℤ) i j n hij ≫
    (HomologicalComplex.mapBifunctorMap f (𝟙 K) (curriedTensor (ModuleCat.{0} R)) (.up ℤ)).f n
  simp only [Cochain.ofHom_v, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f]
  rw [((curriedTensor (ModuleCat.{0} R)).obj (Q.X i)).map_id, Category.id_comp]

@[reassoc]
theorem ι_d (n m i j i' j' : ℤ) (hnm : n + 1 = m) (hij : i + j = n)
    (hi : i + 1 = i') (hj : j + 1 = j') :
    HomologicalComplex.ιMapBifunctor P K (curriedTensor (ModuleCat.{0} R)) (.up ℤ) i j n hij ≫
        ((Homotopy.complexFunctor R K).obj P).d n m =
      ((curriedTensor (ModuleCat.{0} R)).map (P.d i i')).app (K.X j) ≫
        HomologicalComplex.ιMapBifunctor P K (curriedTensor (ModuleCat.{0} R)) (.up ℤ)
          i' j m (by change i' + j = m; omega) +
      i.negOnePow • (((curriedTensor (ModuleCat.{0} R)).obj (P.X i)).map (K.d j j') ≫
        HomologicalComplex.ιMapBifunctor P K (curriedTensor (ModuleCat.{0} R)) (.up ℤ)
          i j' m (by change i + j' = m; omega)) := by
  change _ ≫ (HomologicalComplex.mapBifunctor P K (curriedTensor (ModuleCat.{0} R)) (.up ℤ)).d n m = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq P K (curriedTensor (ModuleCat.{0} R)) (.up ℤ)
      (show (ComplexShape.up ℤ).Rel i i' from hi) j m (by change i' + j = m; omega),
    HomologicalComplex.mapBifunctor.d₂_eq P K (curriedTensor (ModuleCat.{0} R)) (.up ℤ)
      i (show (ComplexShape.up ℤ).Rel j j' from hj) m (by change i + j' = m; omega)]
  change (1 : ℤˣ) • _ + i.negOnePow • _ = _
  rw [one_smul]

theorem map_δ_succ (z : Cochain P Q a) :
    Tensor.Cochain.map R K (δ a (a + 1) z) = δ a (a + 1) (Tensor.Cochain.map R K z) := by
  apply Cochain.ext
  intro n m hnm
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  rw [ι_map R K _ n m i j hnm hij,
    δ_v a (a + 1) rfl z i (i + (a + 1)) rfl (i + a) (i + 1) (by omega) rfl,
    δ_v a (a + 1) rfl (Tensor.Cochain.map R K z) n m hnm (n + a) (n + 1) (by omega) rfl]
  simp only [Functor.map_add, NatTrans.app_add, Preadditive.add_comp, Preadditive.comp_add,
    Functor.map_units_smul, NatTrans.app_units_zsmul, Linear.units_smul_comp,
    Linear.comp_units_smul, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [ι_map_assoc R K z n (n + a) i j rfl hij,
    ι_d R K (n + a) m (i + a) j (i + (a + 1)) (j + 1) (by omega) (by omega) (by omega) rfl,
    ι_d_assoc R K n (n + 1) i j (i + 1) (j + 1) rfl hij rfl rfl]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc]
  rw [ι_map_v R K z (n + 1) m (i + 1) j (i + (a + 1)) (by omega) (by omega) (by omega),
    ι_map_v R K z (n + 1) m i (j + 1) (i + a) (by omega) (by omega) rfl]
  rw [← NatTrans.naturality_assoc]
  simp only [Int.negOnePow_add, Int.negOnePow_one, mul_neg, mul_one,
    smul_smul, smul_add, Units.neg_smul]
  simp only [neg_mul, Units.neg_smul, mul_comm a.negOnePow i.negOnePow]
  abel

theorem map_δ (z : Cochain P Q a) (b : ℤ) :
    Tensor.Cochain.map R K (δ a b z) = δ a b (Tensor.Cochain.map R K z) := by
  by_cases h : a + 1 = b
  · subst b
    exact map_δ_succ R K z
  · rw [δ_shape a b h, δ_shape a b h, Tensor.Cochain.map_zero]

def mapCocycle (z : Cocycle P Q a) :
    Cocycle ((Homotopy.complexFunctor R K).obj P)
      ((Homotopy.complexFunctor R K).obj Q) a :=
  Cocycle.mk (Tensor.Cochain.map R K z.1) (a + 1) rfl (by
    rw [← map_δ, Cocycle.δ_eq_zero, Tensor.Cochain.map_zero])

@[simp]
theorem mapCocycle_coe (z : Cocycle P Q a) : (mapCocycle R K z).1 = Tensor.Cochain.map R K z.1 := rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Cochain
