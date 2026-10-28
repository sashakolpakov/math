import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.Flat.Basic

/-! # Tensor Units -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.TensorUnits

noncomputable section

section

/-! A regular unit on a flat scalar-extended affine chart is defined
over a finitely generated subalgebra of the ambient parameter algebra. -/

open scoped TensorProduct

variable {A R B : Type*} [CommRing A] [CommRing R] [CommRing B] [Algebra A R] [Algebra A B]

theorem subalgebraTensorMap_inclusion {S T : Subalgebra A R} (hST : S ≤ T)
    (x : S ⊗[A] B) :
    Algebra.TensorProduct.map T.val (AlgHom.id A B)
      (Algebra.TensorProduct.map (Subalgebra.inclusion hST) (AlgHom.id A B) x) =
      Algebra.TensorProduct.map S.val (AlgHom.id A B) x := by
  have h : (Algebra.TensorProduct.map T.val (AlgHom.id A B)).comp
      (Algebra.TensorProduct.map (Subalgebra.inclusion hST) (AlgHom.id A B)) =
      Algebra.TensorProduct.map S.val (AlgHom.id A B) := by
    rw [← Algebra.TensorProduct.map_comp, Subalgebra.val_comp_inclusion, AlgHom.id_comp]
  exact DFunLike.congr_fun h x

theorem subalgebraTensorMap_mem_range_mono {S T : Subalgebra A R} (hST : S ≤ T)
    {x : R ⊗[A] B} (hx : x ∈ LinearMap.range (S.val.toLinearMap.rTensor B)) :
    x ∈ LinearMap.range (T.val.toLinearMap.rTensor B) := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨Algebra.TensorProduct.map (Subalgebra.inclusion hST) (AlgHom.id A B) y, ?_⟩
  exact (subalgebraTensorMap_inclusion hST y).trans hy

theorem exists_fg_subalgebra_tensor_unit [Module.Flat A B] (u : (R ⊗[A] B)ˣ) :
    ∃ S : Subalgebra A R, S.FG ∧ ∃ v : (S ⊗[A] B)ˣ,
      Algebra.TensorProduct.map S.val (AlgHom.id A B) (v : S ⊗[A] B) = u := by
  obtain ⟨S, hS, hs⟩ := TensorProduct.Algebra.exists_of_fg (u : R ⊗[A] B)
  obtain ⟨T, hT, ht⟩ := TensorProduct.Algebra.exists_of_fg u.inv
  obtain ⟨x, hx⟩ := subalgebraTensorMap_mem_range_mono (show S ≤ S ⊔ T from le_sup_left) hs
  obtain ⟨y, hy⟩ := subalgebraTensorMap_mem_range_mono (show T ≤ S ⊔ T from le_sup_right) ht
  have hi : Function.Injective (Algebra.TensorProduct.map (S ⊔ T).val (AlgHom.id A B)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (S ⊔ T).val.toLinearMap Subtype.val_injective
  have hxy : x * y = 1 := by
    apply hi
    rw [map_mul, map_one]
    change ((S ⊔ T).val.toLinearMap.rTensor B x) * ((S ⊔ T).val.toLinearMap.rTensor B y) = 1
    rw [hx, hy]
    exact u.val_inv
  exact ⟨S ⊔ T, hS.sup hT, ⟨x, y, hxy, (mul_comm y x).trans hxy⟩, hx⟩

end

section

/-! Finitely many regular units on flat affine charts are all defined
over one finitely generated parameter subalgebra. -/

open scoped TensorProduct

theorem subalgebra_fg_finset_sup {A R ι : Type*} [CommRing A] [CommRing R] [Algebra A R]
    (S : ι → Subalgebra A R) (hS : ∀ i, (S i).FG) (s : Finset ι) : (s.sup S).FG := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty] using (Subalgebra.fg_bot (R := A) (A := R))
  | @insert i s _ ih => simpa only [Finset.sup_insert] using (hS i).sup ih

theorem exists_fg_subalgebra_finite_tensor_units
    {A R ι : Type*} [CommRing A] [CommRing R] [Algebra A R] [Fintype ι]
    (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Module.Flat A (B i)]
    (u : ∀ i, (R ⊗[A] B i)ˣ) :
    ∃ S : Subalgebra A R, S.FG ∧ ∃ v : ∀ i, (S ⊗[A] B i)ˣ,
      ∀ i, Algebra.TensorProduct.map S.val (AlgHom.id A (B i)) (v i : S ⊗[A] B i) = u i := by
  classical
  choose S hS v hv using fun i => exists_fg_subalgebra_tensor_unit (u i)
  let T : Subalgebra A R := Finset.univ.sup S
  have hST (i : ι) : S i ≤ T := Finset.le_sup (Finset.mem_univ i)
  refine ⟨T, subalgebra_fg_finset_sup S hS Finset.univ,
    (fun i => Units.map (Algebra.TensorProduct.map (Subalgebra.inclusion (hST i))
      (AlgHom.id A (B i))).toMonoidHom (v i)), ?_⟩
  intro i
  change Algebra.TensorProduct.map T.val (AlgHom.id A (B i))
      (Algebra.TensorProduct.map (Subalgebra.inclusion (hST i)) (AlgHom.id A (B i)) (v i : S i ⊗[A] B i)) = _
  exact (subalgebraTensorMap_inclusion (hST i) (v i : S i ⊗[A] B i)).trans (hv i)

end

/-! Finite coefficient descent in the tensor order used by native
affine base-change coordinates. -/

open scoped TensorProduct

theorem exists_fg_subalgebra_finite_right_tensor_units
    {A R ι : Type*} [CommRing A] [CommRing R] [Algebra A R] [Fintype ι]
    (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Module.Flat A (B i)]
    (u : ∀ i, (B i ⊗[A] R)ˣ) :
    ∃ S : Subalgebra A R, S.FG ∧ ∃ v : ∀ i, (B i ⊗[A] S)ˣ,
      ∀ i, Algebra.TensorProduct.map (AlgHom.id A (B i)) S.val (v i : B i ⊗[A] S) = u i := by
  let w (i) := Units.map (Algebra.TensorProduct.comm A (B i) R).toMonoidHom (u i)
  obtain ⟨S, hS, v, hv⟩ := exists_fg_subalgebra_finite_tensor_units B w
  refine ⟨S, hS, (fun i => Units.map (Algebra.TensorProduct.comm A S (B i)).toMonoidHom (v i)), ?_⟩
  intro i
  change Algebra.TensorProduct.map (AlgHom.id A (B i)) S.val
    (Algebra.TensorProduct.comm A S (B i) (v i : S ⊗[A] B i)) = _
  rw [← Algebra.TensorProduct.comm_comp_map_apply, hv i]
  change Algebra.TensorProduct.comm A R (B i)
    (Algebra.TensorProduct.comm A (B i) R (u i : B i ⊗[A] R)) = _
  exact (Algebra.TensorProduct.comm A (B i) R).symm_apply_apply _

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.TensorUnits
