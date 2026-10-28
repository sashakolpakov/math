import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappingConeContractions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BaseChangeComplex
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.Single
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.SequenceBasic

/-! # Koszul Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.KoszulComplex

noncomputable section

/-! The scalar Koszul complex is an iterated mapping cone in degrees minus the number of parameters through zero. On every field-valued coefficient map where one parameter survives, its actual scalar extension contracts. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R]

def scalarKoszulComplex (M : ModuleCat.{u} R) : List R → CochainComplex (ModuleCat.{u} R) ℤ
  | [] => (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj M
  | r :: rs => CochainComplex.mappingCone (r • 𝟙 (scalarKoszulComplex M rs))

theorem scalarKoszulComplex_isZero_X (M : ModuleCat.{u} R) (rs : List R) (i : ℤ)
    (hi : i < -(rs.length : ℤ) ∨ 0 < i) : IsZero ((KoszulComplex.scalarKoszulComplex M rs).X i) := by
  induction rs generalizing i with
  | nil =>
    apply HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i
    simp only [List.length_nil, Nat.cast_zero, neg_zero] at hi
    omega
  | cons r rs ih =>
    apply (CochainComplex.mappingCone.isZero_X_iff _ i).mpr
    constructor
    · apply ih
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hi
      omega
    · apply ih
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hi
      omega

theorem field_baseChange_scalar_id_isIso
    (B : Type u) [Field B] [Algebra R B]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (r : R) (hr : algebraMap R B r ≠ 0) :
    IsIso (((Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℤ)).map
      (r • 𝟙 C)) := by
  let F := Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B
  let BC := (F.mapHomologicalComplex (.up ℤ)).obj C
  let s := algebraMap R B r
  have heq : (F.mapHomologicalComplex (.up ℤ)).map (r • 𝟙 C) = s • 𝟙 BC := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    change (r • (LinearMap.id : C.X i →ₗ[R] C.X i)).baseChange B =
      s • (LinearMap.id : B ⊗[R] C.X i →ₗ[B] B ⊗[R] C.X i)
    rw [LinearMap.baseChange_smul, LinearMap.baseChange_id]
    exact (IsScalarTower.algebraMap_smul B r
      (LinearMap.id : B ⊗[R] C.X i →ₗ[B] B ⊗[R] C.X i)).symm
  let e : BC ≅ BC := {
    hom := s • 𝟙 BC
    inv := s⁻¹ • 𝟙 BC
    hom_inv_id := by simp [Linear.comp_smul, smul_smul, s, hr]
    inv_hom_id := by simp [Linear.comp_smul, smul_smul, s, hr] }
  rw [heq]
  exact e.isIso_hom

theorem scalarKoszulComplex_field_contractible
    (B : Type u) [Field B] [Algebra R B] (M : ModuleCat.{u} R) (rs : List R)
    (h : ∃ r ∈ rs, algebraMap R B r ≠ 0) :
    Nonempty (Homotopy
      (𝟙 (((Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℤ)).obj
        (KoszulComplex.scalarKoszulComplex M rs))) 0) := by
  let F := Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B
  induction rs with
  | nil => simp at h
  | cons r rs ih =>
    let C := KoszulComplex.scalarKoszulComplex M rs
    let f := r • 𝟙 C
    let e := CochainComplex.mappingCone.mapHomologicalComplexIso f F
    apply MappingConeContractions.cochainContractible_of_iso e
    obtain ⟨s, hs, hsn⟩ := h
    rcases List.mem_cons.mp hs with rfl | hs
    · have : IsIso ((F.mapHomologicalComplex (.up ℤ)).map (s • 𝟙 C)) :=
        field_baseChange_scalar_id_isIso B C s hsn
      exact ⟨MappingConeContractions.mappingConeHomotopyToZeroOfIso _⟩
    · have hc := ih ⟨s, hs, hsn⟩
      exact MappingConeContractions.mappingCone_contractible_of_contractible _ hc hc

theorem scalarKoszulComplex_field_contractible_off_ideal
    (B : Type u) [Field B] [Algebra R B] (M : ModuleCat.{u} R) (rs : List R)
    (h : ¬ Regular.SequenceBasic.Ideal.ofList rs ≤ RingHom.ker (algebraMap R B)) :
    Nonempty (Homotopy
      (𝟙 (((Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℤ)).obj
        (KoszulComplex.scalarKoszulComplex M rs))) 0) := by
  apply scalarKoszulComplex_field_contractible B M rs
  by_contra hn
  apply h
  apply Ideal.span_le.mpr
  intro r hr
  change algebraMap R B r = 0
  by_contra hrn
  exact hn ⟨r, hr, hrn⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.KoszulComplex
