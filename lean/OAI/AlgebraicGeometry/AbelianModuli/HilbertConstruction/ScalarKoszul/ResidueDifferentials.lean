import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.KoszulComplex

/-! # Residue Differentials -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.ResidueDifferentials

noncomputable section

/-! When a coefficient map kills every parameter, every differential of the actual base-changed scalar Koszul complex is zero. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CochainComplex
open scoped TensorProduct
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem zero_differentials_of_iso
    {V : Type u} [Category.{v} V] [HasZeroMorphisms V]
    {ι : Type*} {c : ComplexShape ι} {C D : HomologicalComplex V c}
    (e : C ≅ D) (hD : ∀ i j, D.d i j = 0) : ∀ i j, C.d i j = 0 := by
  intro i j
  apply (cancel_mono (e.hom.f j)).mp
  rw [← e.hom.comm i j, hD i j, comp_zero, zero_comp]

theorem mappingCone_zero_differentials
    {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]
    (C : CochainComplex V ℤ) (f : C ⟶ C)
    (hf : ∀ i, f.f i = 0) (hC : ∀ i j, C.d i j = 0) :
    ∀ i j, (mappingCone f).d i j = 0 := by
  intro i j
  by_cases hij : i + 1 = j
  · apply mappingCone.ext_to f j (j + 1) rfl
    · rw [mappingCone.d_fst_v f i j (j + 1) hij rfl, hC j (j + 1), comp_zero, zero_comp, neg_zero]
    · rw [mappingCone.d_snd_v f i j hij, hf j, hC i j, comp_zero, comp_zero, add_zero, zero_comp]
  · exact (mappingCone f).shape i j hij

variable {R : Type u} [CommRing R]

theorem baseChange_scalar_id_zero
    (B : Type u) [CommRing B] [Algebra R B]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (r : R) (hr : algebraMap R B r = 0) :
    ((Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℤ)).map
      (r • 𝟙 C) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  change (r • (LinearMap.id : C.X i →ₗ[R] C.X i)).baseChange B = 0
  rw [LinearMap.baseChange_smul, LinearMap.baseChange_id,
    ← IsScalarTower.algebraMap_smul B r
      (LinearMap.id : B ⊗[R] C.X i →ₗ[B] B ⊗[R] C.X i), hr, zero_smul]

theorem scalarKoszulComplex_baseChange_d_zero
    (B : Type u) [CommRing B] [Algebra R B] (M : ModuleCat.{u} R)
    (rs : List R) (hrs : ∀ r ∈ rs, algebraMap R B r = 0) :
    ∀ i j, (((Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℤ)).obj
      (KoszulComplex.scalarKoszulComplex M rs)).d i j = 0 := by
  let F := Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B
  induction rs with
  | nil =>
    intro i j
    change F.map ((KoszulComplex.scalarKoszulComplex M []).d i j) = 0
    rw [show (KoszulComplex.scalarKoszulComplex M []).d i j = 0 from rfl, F.map_zero]
  | cons r rs ih =>
    let C := KoszulComplex.scalarKoszulComplex M rs
    let f := r • 𝟙 C
    let e := mappingCone.mapHomologicalComplexIso f F
    apply zero_differentials_of_iso e
    apply mappingCone_zero_differentials
    · have hf := baseChange_scalar_id_zero B C r (hrs r (List.mem_cons_self))
      intro i
      exact congrArg (fun a => a.f i) hf
    · exact ih (fun s hs => hrs s (List.mem_cons_of_mem r hs))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.ResidueDifferentials
