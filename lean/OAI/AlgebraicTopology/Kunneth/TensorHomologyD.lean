import OAI.AlgebraicTopology.Kunneth.ChainSplittingD
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.DirectSum.Module

/-! # Tensor Homology D -/

namespace OAI.AlgebraicTopology.Kunneth.TensorHomologyD

noncomputable section

section

/-! The algebraic tensor-product homology comparison used in Kunneth. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting
open scoped DirectSum TensorProduct

namespace Construction.TensorHomology

variable {k : Type} [Field k]

def tensorHomotopyLeft
    {A B C D : ChainComplex (ModuleCat.{0} k) ℕ}
    {f g : A ⟶ C} (h : Homotopy f g) (u : B ⟶ D) :
    Homotopy (f ⊗ₘ u) (g ⊗ₘ u) :=
  HomologicalComplex.mapBifunctorMapHomotopy₁ h u
    (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ)

def tensorHomotopyRight
    {A B C D : ChainComplex (ModuleCat.{0} k) ℕ}
    (f : A ⟶ C) {u v : B ⟶ D} (h : Homotopy u v) :
    Homotopy (f ⊗ₘ u) (f ⊗ₘ v) :=
  HomologicalComplex.mapBifunctorMapHomotopy₂ f h
    (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ)

/-- Tensor products preserve chain homotopy equivalences. -/
def tensorHomotopyEquiv
    {A B C D : ChainComplex (ModuleCat.{0} k) ℕ}
    (e : HomotopyEquiv A C) (f : HomotopyEquiv B D) :
    HomotopyEquiv (A ⊗ B) (C ⊗ D) where
  hom := e.hom ⊗ₘ f.hom
  inv := e.inv ⊗ₘ f.inv
  homotopyHomInvId :=
    (Homotopy.ofEq (tensorHom_comp_tensorHom _ _ _ _)).trans
      ((tensorHomotopyLeft e.homotopyHomInvId (f.hom ≫ f.inv)).trans
        ((tensorHomotopyRight (𝟙 A) f.homotopyHomInvId).trans
          (Homotopy.ofEq (id_tensorHom_id A B))))
  homotopyInvHomId :=
    (Homotopy.ofEq (tensorHom_comp_tensorHom _ _ _ _)).trans
      ((tensorHomotopyLeft e.homotopyInvHomId (f.inv ≫ f.hom)).trans
        ((tensorHomotopyRight (𝟙 C) f.homotopyInvHomId).trans
          (Homotopy.ofEq (id_tensorHom_id C D))))

variable (C D : ChainComplex (ModuleCat.{0} k) ℕ)

/-- Splitting both factors gives a homotopy equivalence for their tensor product. -/
def tensorHomologySplitting :
    HomotopyEquiv (ChainSplittingD.Construction.ChainSplitting.homologyComplex C ⊗ ChainSplittingD.Construction.ChainSplitting.homologyComplex D) (C ⊗ D) :=
  tensorHomotopyEquiv (ChainSplittingD.Construction.ChainSplitting.homologyHomotopyEquiv C) (ChainSplittingD.Construction.ChainSplitting.homologyHomotopyEquiv D)

/-- Tensoring complexes with zero differentials again gives zero differential. -/
theorem tensorHomology_d_zero (n m : ℕ) :
    (ChainSplittingD.Construction.ChainSplitting.homologyComplex C ⊗ ChainSplittingD.Construction.ChainSplitting.homologyComplex D).d n m = 0 := by
  change (HomologicalComplex.mapBifunctor (ChainSplittingD.Construction.ChainSplitting.homologyComplex C) (ChainSplittingD.Construction.ChainSplitting.homologyComplex D)
    (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ)).d n m = 0
  rw [HomologicalComplex.mapBifunctor.d_eq]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    comp_zero]
  have h1 : HomologicalComplex.mapBifunctor.d₁ (ChainSplittingD.Construction.ChainSplitting.homologyComplex C) (ChainSplittingD.Construction.ChainSplitting.homologyComplex D)
      (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ) i j m = 0 := by
    by_cases hi : (ComplexShape.down ℕ).Rel i ((ComplexShape.down ℕ).next i)
    · rw [HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ hi]
      simp only [ChainSplittingD.Construction.ChainSplitting.homologyComplex, Functor.map_zero, zero_app, zero_comp, smul_zero]
    · exact HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ i j m hi
  have h2 : HomologicalComplex.mapBifunctor.d₂ (ChainSplittingD.Construction.ChainSplitting.homologyComplex C) (ChainSplittingD.Construction.ChainSplitting.homologyComplex D)
      (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ) i j m = 0 := by
    by_cases hj : (ComplexShape.down ℕ).Rel j ((ComplexShape.down ℕ).next j)
    · rw [HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ i hj]
      simp only [ChainSplittingD.Construction.ChainSplitting.homologyComplex, Functor.map_zero, zero_comp, smul_zero]
    · exact HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ i j m hj
  rw [h1, h2, add_zero]

/-- Homology of a zero-differential complex is its degree object. -/
def zeroDifferentialHomologyIso (K : ChainComplex (ModuleCat.{0} k) ℕ)
    (hd : ∀ i j, K.d i j = 0) (n : ℕ) : K.homology n ≅ K.X n :=
  (ShortComplex.HomologyData.ofZeros (K.sc n)
    (hd _ _) (hd _ _)).left.homologyIso

/-- The degree-n tensor sum of homology groups computes the tensor-complex homology. -/
def tensorHomologyIso (n : ℕ) :
    (ChainSplittingD.Construction.ChainSplitting.homologyComplex C ⊗ ChainSplittingD.Construction.ChainSplitting.homologyComplex D).X n ≅ (C ⊗ D).homology n :=
  (zeroDifferentialHomologyIso (ChainSplittingD.Construction.ChainSplitting.homologyComplex C ⊗ ChainSplittingD.Construction.ChainSplitting.homologyComplex D)
    (tensorHomology_d_zero C D) n).symm ≪≫ (tensorHomologySplitting C D).toHomologyIso n

abbrev DegreePairs (n : ℕ) := {ij : ℕ × ℕ // ij.1 + ij.2 = n}

abbrev TensorDegreeSum (n : ℕ) :=
  ⨁ ij : DegreePairs n, C.X ij.val.1 ⊗[k] D.X ij.val.2

/-- The concrete direct sum and the native total-complex degree have the
 same summand inclusions. -/
def tensorDegreeIn (n : ℕ) :
    ModuleCat.of k (TensorDegreeSum C D n) ⟶ (C ⊗ D).X n :=
  ModuleCat.ofHom (DirectSum.toModule k (DegreePairs n) ((C ⊗ D).X n)
    (fun ij => (HomologicalComplex.ιTensorObj C D ij.val.1 ij.val.2 n ij.property).hom))

def tensorDegreeOut (n : ℕ) :
    (C ⊗ D).X n ⟶ ModuleCat.of k (TensorDegreeSum C D n) :=
  HomologicalComplex.mapBifunctorDesc (fun i j hij =>
    ModuleCat.ofHom (DirectSum.lof k (DegreePairs n)
      (fun ij => C.X ij.val.1 ⊗[k] D.X ij.val.2) ⟨(i, j), hij⟩))

@[simp]
theorem tensorDegreeIn_lof (n : ℕ) (ij : DegreePairs n)
    (x : C.X ij.val.1 ⊗[k] D.X ij.val.2) :
    tensorDegreeIn C D n
        (DirectSum.lof k (DegreePairs n)
          (fun d => C.X d.val.1 ⊗[k] D.X d.val.2) ij x) =
      HomologicalComplex.ιTensorObj C D ij.val.1 ij.val.2 n ij.property x :=
  DirectSum.toModule_lof k _ _

@[reassoc (attr := simp)]
theorem ι_tensorDegreeOut (n i j : ℕ) (hij : i + j = n) :
    HomologicalComplex.ιTensorObj C D i j n hij ≫ tensorDegreeOut C D n =
      ModuleCat.ofHom (DirectSum.lof k (DegreePairs n)
        (fun d => C.X d.val.1 ⊗[k] D.X d.val.2) ⟨(i, j), hij⟩) :=
  HomologicalComplex.ι_mapBifunctorDesc _ i j hij

theorem tensorDegreeIn_out (n : ℕ) :
    tensorDegreeIn C D n ≫ tensorDegreeOut C D n =
      𝟙 (ModuleCat.of k (TensorDegreeSum C D n)) := by
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro ij
  apply LinearMap.ext
  intro x
  change tensorDegreeOut C D n
      (tensorDegreeIn C D n
        (DirectSum.lof k (DegreePairs n)
          (fun d => C.X d.val.1 ⊗[k] D.X d.val.2) ij x)) = _
  rw [tensorDegreeIn_lof]
  exact ConcreteCategory.congr_hom
    (ι_tensorDegreeOut C D n ij.val.1 ij.val.2 ij.property) x

theorem tensorDegreeOut_in (n : ℕ) :
    tensorDegreeOut C D n ≫ tensorDegreeIn C D n = 𝟙 ((C ⊗ D).X n) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [← Category.assoc, ι_tensorDegreeOut]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact tensorDegreeIn_lof C D n ⟨(i, j), hij⟩ x

def tensorDegreeIso (n : ℕ) :
    ModuleCat.of k (TensorDegreeSum C D n) ≅ (C ⊗ D).X n where
  hom := tensorDegreeIn C D n
  inv := tensorDegreeOut C D n
  hom_inv_id := tensorDegreeIn_out C D n
  inv_hom_id := tensorDegreeOut_in C D n

/-- Algebraic Künneth over a field, for genuine nonnegative chain complexes. -/
def algebraicKunneth (n : ℕ) :
    (⨁ ij : DegreePairs n, C.homology ij.val.1 ⊗[k] D.homology ij.val.2) ≃ₗ[k]
      (C ⊗ D).homology n :=
  (tensorDegreeIso (ChainSplittingD.Construction.ChainSplitting.homologyComplex C) (ChainSplittingD.Construction.ChainSplitting.homologyComplex D) n ≪≫
    tensorHomologyIso C D n).toLinearEquiv

/-- Tensoring two complexes whose homology is concentrated in degree zero
 again produces no positive-degree homology. -/
theorem tensorHomology_isZero_of_positive
    (hC : ∀ n : ℕ, n ≠ 0 → IsZero (C.homology n))
    (hD : ∀ n : ℕ, n ≠ 0 → IsZero (D.homology n))
    (n : ℕ) (hn : n ≠ 0) : IsZero ((C ⊗ D).homology n) := by
  let (ij : DegreePairs n) :
      Subsingleton (C.homology ij.val.1 ⊗[k] D.homology ij.val.2) := by
    by_cases hi : ij.val.1 = 0
    · have hj : ij.val.2 ≠ 0 := by
        intro hj
        apply hn
        exact ij.property.symm.trans (by rw [hi, hj])
      let := ModuleCat.subsingleton_of_isZero (hD ij.val.2 hj)
      infer_instance
    · let := ModuleCat.subsingleton_of_isZero (hC ij.val.1 hi)
      infer_instance
  let : Subsingleton ((C ⊗ D).homology n) :=
    (algebraicKunneth C D n).symm.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end Construction.TensorHomology

end

/-! Low-degree tensor-complex formulas for Kunneth's chain comparison. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex
open scoped TensorProduct

namespace Construction.TensorLowDegrees

variable {k : Type} [Field k]
variable (C D : ChainComplex (ModuleCat.{0} k) ℕ)

def zeroProjection : (C ⊗ D).X 0 ⟶ C.X 0 ⊗ D.X 0 :=
  mapBifunctorDesc (fun p q hpq => eqToHom (by
    obtain ⟨hp, hq⟩ := Nat.add_eq_zero_iff.mp hpq
    subst p q
    rfl))

@[reassoc (attr := simp)]
theorem zeroInclusion_projection :
    ιTensorObj C D 0 0 0 rfl ≫ zeroProjection C D = 𝟙 _ := by
  unfold zeroProjection
  erw [ι_mapBifunctorDesc]
  rfl

theorem zeroProjection_inclusion :
    zeroProjection C D ≫ ιTensorObj C D 0 0 0 rfl = 𝟙 ((C ⊗ D).X 0) := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  obtain ⟨hp, hq⟩ := Nat.add_eq_zero_iff.mp hpq
  subst p q
  rw [← Category.assoc, zeroInclusion_projection]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

def degreeZeroIso : C.X 0 ⊗ D.X 0 ≅ (C ⊗ D).X 0 where
  hom := ιTensorObj C D 0 0 0 rfl
  inv := zeroProjection C D
  hom_inv_id := zeroInclusion_projection C D
  inv_hom_id := zeroProjection_inclusion C D

@[reassoc]
theorem inclusion10_d :
    ιTensorObj C D 1 0 1 rfl ≫ (C ⊗ D).d 1 0 =
      (C.d 1 0 ⊗ₘ 𝟙 (D.X 0)) ≫ ιTensorObj C D 0 0 0 rfl := by
  change ιMapBifunctor C D (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ)
    1 0 1 rfl ≫ (mapBifunctor C D (curriedTensor (ModuleCat.{0} k))
      (ComplexShape.down ℕ)).d 1 0 = _
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq C D _ _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl) 0 0 rfl,
    mapBifunctor.d₂_eq_zero C D _ _ 1 0 0 (by simp), add_zero]
  change (1 : ℤˣ) • ((C.d 1 0 ▷ D.X 0) ≫ ιTensorObj C D 0 0 0 rfl) = _
  rw [one_smul, tensorHom_id]

@[reassoc]
theorem inclusion01_d :
    ιTensorObj C D 0 1 1 rfl ≫ (C ⊗ D).d 1 0 =
      (𝟙 (C.X 0) ⊗ₘ D.d 1 0) ≫ ιTensorObj C D 0 0 0 rfl := by
  change ιMapBifunctor C D (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ)
    0 1 1 rfl ≫ (mapBifunctor C D (curriedTensor (ModuleCat.{0} k))
      (ComplexShape.down ℕ)).d 1 0 = _
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq_zero C D _ _ 0 1 0 (by simp), zero_add,
    mapBifunctor.d₂_eq C D _ _ 0 (show (ComplexShape.down ℕ).Rel 1 0 from rfl) 0 rfl]
  change ((-1 : ℤˣ) ^ 0) • ((C.X 0 ◁ D.d 1 0) ≫ ιTensorObj C D 0 0 0 rfl) = _
  rw [pow_zero, one_smul, id_tensorHom]

@[simp]
theorem inclusion10_d_apply (x : C.X 1) (y : D.X 0) :
    (C ⊗ D).d 1 0 (ιTensorObj C D 1 0 1 rfl (x ⊗ₜ[k] y)) =
      ιTensorObj C D 0 0 0 rfl (C.d 1 0 x ⊗ₜ[k] y) := by
  have h := ConcreteCategory.congr_hom (inclusion10_d C D) (x ⊗ₜ[k] y)
  change (C ⊗ D).d 1 0 (ιTensorObj C D 1 0 1 rfl (x ⊗ₜ[k] y)) =
    ιTensorObj C D 0 0 0 rfl (TensorProduct.map (C.d 1 0).hom LinearMap.id (x ⊗ₜ[k] y)) at h
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply] using h

@[simp]
theorem inclusion01_d_apply (x : C.X 0) (y : D.X 1) :
    (C ⊗ D).d 1 0 (ιTensorObj C D 0 1 1 rfl (x ⊗ₜ[k] y)) =
      ιTensorObj C D 0 0 0 rfl (x ⊗ₜ[k] D.d 1 0 y) := by
  have h := ConcreteCategory.congr_hom (inclusion01_d C D) (x ⊗ₜ[k] y)
  change (C ⊗ D).d 1 0 (ιTensorObj C D 0 1 1 rfl (x ⊗ₜ[k] y)) =
    ιTensorObj C D 0 0 0 rfl (TensorProduct.map LinearMap.id (D.d 1 0).hom (x ⊗ₜ[k] y)) at h
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply] using h

end Construction.TensorLowDegrees

end

end OAI.AlgebraicTopology.Kunneth.TensorHomologyD
