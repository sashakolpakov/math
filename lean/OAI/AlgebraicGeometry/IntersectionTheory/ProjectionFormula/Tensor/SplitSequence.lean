import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.MappingCone
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-! # Split Sequence -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SplitSequence

noncomputable section

/-! Tensoring preserves degreewise split short exact sequences, with the
splittings obtained from the actual homogeneous cochain tensor map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CochainComplex _root_.CochainComplex.HomComplex

variable (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℤ)
  (S : ShortComplex (CochainComplex (ModuleCat.{0} R) ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval _ _ n)).Splitting)

def retraction : Cochain S.X₂ S.X₁ 0 := Cochain.ofHoms (fun n => (σ n).r)

def sectionCochain : Cochain S.X₃ S.X₂ 0 := Cochain.ofHoms (fun n => (σ n).s)

theorem f_retraction : (Cochain.ofHom S.f).comp (retraction R S σ) (zero_add 0) = Cochain.ofHom (𝟙 _) := by
  apply Cochain.ext₀
  intro n
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, retraction,
    Cochain.ofHoms_v, HomologicalComplex.id_f]
  exact (σ n).f_r

theorem section_g : (sectionCochain R S σ).comp (Cochain.ofHom S.g) (zero_add 0) = Cochain.ofHom (𝟙 _) := by
  apply Cochain.ext₀
  intro n
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, sectionCochain,
    Cochain.ofHoms_v, HomologicalComplex.id_f]
  exact (σ n).s_g

theorem decomposition :
    (retraction R S σ).comp (Cochain.ofHom S.f) (zero_add 0) +
      (Cochain.ofHom S.g).comp (sectionCochain R S σ) (zero_add 0) = Cochain.ofHom (𝟙 _) := by
  apply Cochain.ext₀
  intro n
  simp only [Cochain.add_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    retraction, sectionCochain, Cochain.ofHoms_v, HomologicalComplex.id_f]
  exact (σ n).id

def mappedSequence : ShortComplex (CochainComplex (ModuleCat.{0} R) ℤ) :=
  S.map (Homotopy.complexFunctor R K)

def splitting (n : ℤ) :
    ((mappedSequence R K S).map (HomologicalComplex.eval _ _ n)).Splitting where
  r := (Tensor.Cochain.map R K (retraction R S σ)).v n n (add_zero n)
  s := (Tensor.Cochain.map R K (sectionCochain R S σ)).v n n (add_zero n)
  f_r := by
    change ((Homotopy.complexFunctor R K).map S.f).f n ≫ _ =
      𝟙 (((Homotopy.complexFunctor R K).obj S.X₁).X n)
    have h := congrArg (Tensor.Cochain.map R K) (f_retraction R S σ)
    rw [Tensor.Cochain.map_comp, Tensor.Cochain.map_ofHom,
      Tensor.Cochain.map_ofHom, CategoryTheory.Functor.map_id] at h
    simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.id_f]
      using Cochain.congr_v h n n (add_zero n)
  s_g := by
    change _ ≫ ((Homotopy.complexFunctor R K).map S.g).f n =
      𝟙 (((Homotopy.complexFunctor R K).obj S.X₃).X n)
    have h := congrArg (Tensor.Cochain.map R K) (section_g R S σ)
    rw [Tensor.Cochain.map_comp, Tensor.Cochain.map_ofHom,
      Tensor.Cochain.map_ofHom, CategoryTheory.Functor.map_id] at h
    simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.id_f]
      using Cochain.congr_v h n n (add_zero n)
  id := by
    change (Tensor.Cochain.map R K (retraction R S σ)).v n n (add_zero n) ≫
      ((Homotopy.complexFunctor R K).map S.f).f n +
      ((Homotopy.complexFunctor R K).map S.g).f n ≫
        (Tensor.Cochain.map R K (sectionCochain R S σ)).v n n (add_zero n) =
      𝟙 (((Homotopy.complexFunctor R K).obj S.X₂).X n)
    have h := congrArg (Tensor.Cochain.map R K) (decomposition R S σ)
    rw [Tensor.Cochain.map_add, Tensor.Cochain.map_comp,
      Tensor.Cochain.map_comp, Tensor.Cochain.map_ofHom,
      Tensor.Cochain.map_ofHom, Tensor.Cochain.map_ofHom, CategoryTheory.Functor.map_id] at h
    simpa only [Cochain.add_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.id_f]
      using Cochain.congr_v h n n (add_zero n)

include σ in
theorem shortExact : (mappedSequence R K S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => (splitting R K S σ n).shortExact)

theorem inl_descShortComplex :
    (mappingCone.inl S.f).comp (Cochain.ofHom (mappingCone.descShortComplex S)) (add_zero (-1)) = 0 := by
  rw [mappingCone.descShortComplex, mappingCone.inl_desc]

theorem inv_descShortComplex :
    (MappingCone.iso R K S.f).inv ≫
      (Homotopy.complexFunctor R K).map (mappingCone.descShortComplex S) =
      mappingCone.descShortComplex (mappedSequence R K S) := by
  change MappingCone.inv R K S.f ≫ _ = _
  apply Cochain.ofHom_injective
  rw [Cochain.ofHom_comp, MappingCone.inv_ofHom]
  apply (mappingCone.ext_cochain_from_iff _ (-1) 0 (neg_add_cancel 1)).2
  constructor
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain,
      mappingCone.inl_descCochain, ← Tensor.Cochain.map_ofHom,
      ← Tensor.Cochain.map_comp, inl_descShortComplex, Tensor.Cochain.map_zero]
    exact (inl_descShortComplex R (mappedSequence R K S)).symm
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain,
      mappingCone.inr_descCochain, ← Tensor.Cochain.map_ofHom,
      ← Tensor.Cochain.map_comp, ← Cochain.ofHom_comp,
      mappingCone.inr_descShortComplex, Tensor.Cochain.map_ofHom,
      ← Cochain.ofHom_comp]
    exact (congrArg Cochain.ofHom (mappingCone.inr_descShortComplex (mappedSequence R K S))).symm

theorem hom_descShortComplex :
    (MappingCone.iso R K S.f).hom ≫
      mappingCone.descShortComplex (mappedSequence R K S) =
    (Homotopy.complexFunctor R K).map (mappingCone.descShortComplex S) := by
  rw [← cancel_epi (MappingCone.iso R K S.f).inv,
    Iso.inv_hom_id_assoc, inv_descShortComplex]

include σ in
theorem quasiIso_descShortComplex :
    QuasiIso
      ((Homotopy.complexFunctor R K).map (mappingCone.descShortComplex S)) := by
  let := mappingCone.quasiIso_descShortComplex (SplitSequence.shortExact R K S σ)
  rw [← hom_descShortComplex]
  infer_instance

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SplitSequence
