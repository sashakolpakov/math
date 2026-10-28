import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Domain
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-! # Schematic Closure -/

namespace OAI.AlgebraicGeometry.GroupSchemes.SchematicClosure

/-!
SchematicClosure: schematic closure, expressed by contraction of a generic Hopf ideal.

The quotient by the contracted ideal embeds in the generic quotient, so it
is torsion-free and hence flat over the DVR. The embedding is a localization
map, which identifies the generic fiber and preserves rank. Its tensor square
is injective by flatness, allowing the generic coideal identity to descend.
All imports are proved mathlib results; the statement stub is not imported.
-/

open scoped TensorProduct nonZeroDivisors

variable {R K A : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [HopfAlgebra R A]

abbrev genericInclusion : A →ₐ[R] (K ⊗[R] A) :=
  Algebra.TensorProduct.includeRight

abbrev closureIdeal (I : Ideal (K ⊗[R] A)) : Ideal A :=
  Ideal.comap (genericInclusion (R := R) (K := K) (A := A)).toRingHom I

abbrev closureEmbedding (I : Ideal (K ⊗[R] A)) :
    (A ⧸ closureIdeal I) →ₐ[R] ((K ⊗[R] A) ⧸ I) :=
  Ideal.quotientMapₐ I genericInclusion le_rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
lemma closureEmbedding_injective (I : Ideal (K ⊗[R] A)) :
    Function.Injective (closureEmbedding I) :=
  Ideal.quotientMap_injective

lemma closure_flat (I : Ideal (K ⊗[R] A)) :
    Module.Flat R (A ⧸ closureIdeal I) := by
  have : Module.IsTorsionFree R K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective R K)
  have : Module.IsTorsionFree R ((K ⊗[R] A) ⧸ I) :=
    Module.IsTorsionFree.trans (R := K) (S := R)
  have : Module.IsTorsionFree R (A ⧸ closureIdeal I) :=
    (closureEmbedding_injective I).moduleIsTorsionFree _
      (fun r x => (closureEmbedding I).toLinearMap.map_smul r x)
  exact Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma closure_localized (I : Ideal (K ⊗[R] A)) :
    IsLocalizedModule R⁰ (closureEmbedding I).toLinearMap where
  map_units := (isLocalizedModule_id R⁰ ((K ⊗[R] A) ⧸ I) K).map_units
  surj y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨a, s⟩, h⟩ :=
      IsLocalizedModule.surj R⁰ (TensorProduct.mk R K A 1) x
    change s.val • x = 1 ⊗ₜ[R] a at h
    refine ⟨(Ideal.Quotient.mk (closureIdeal I) a, s), ?_⟩
    change s • Ideal.Quotient.mk I x = Ideal.Quotient.mk I (1 ⊗ₜ[R] a)
    exact (map_smul (Ideal.Quotient.mkₐ R I) s.val x).symm.trans
      (congrArg (Ideal.Quotient.mk I) h)
  exists_of_eq h := ⟨1, by simpa using closureEmbedding_injective I h⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma closure_generic_fiber (I : Ideal (K ⊗[R] A)) :
    Ideal.map genericInclusion.toRingHom (closureIdeal I) = I := by
  apply le_antisymm (Ideal.map_le_iff_le_comap.mpr le_rfl)
  intro x hx
  obtain ⟨⟨a, s⟩, h⟩ :=
    IsLocalizedModule.surj R⁰ (TensorProduct.mk R K A 1) x
  change s.val • x = 1 ⊗ₜ[R] a at h
  have ha : a ∈ closureIdeal I := by
    change 1 ⊗ₜ[R] a ∈ I
    rw [← h]
    exact (I.restrictScalars R).smul_mem s.val hx
  have hmem : (algebraMap R K s.val) • x ∈
      Ideal.map genericInclusion.toRingHom (closureIdeal I) := by
    rw [algebraMap_smul]
    rw [h]
    exact Ideal.mem_map_of_mem _ ha
  exact (Submodule.smul_mem_iff_of_isUnit
    ((Ideal.map genericInclusion.toRingHom (closureIdeal I)).restrictScalars K)
    (IsLocalization.map_units K s)).mp hmem

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma closure_rank (I : Ideal (K ⊗[R] A)) :
    Module.finrank R (A ⧸ closureIdeal I) =
      Module.finrank K ((K ⊗[R] A) ⧸ I) := by
  have := closure_localized I
  rw [IsFractionRing.finrank_right_eq R K ((K ⊗[R] A) ⧸ I)]
  exact (IsLocalizedModule.finrank_eq R⁰ (closureEmbedding I).toLinearMap le_rfl).symm

abbrev tensorToGeneric :
    (A ⊗[R] A) →ₗ[R] ((K ⊗[R] A) ⊗[K] (K ⊗[R] A)) :=
  (TensorProduct.mapOfCompatibleSMul K R R _ _).comp
    (TensorProduct.map genericInclusion.toLinearMap genericInclusion.toLinearMap)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
lemma comul_genericInclusion (a : A) :
    Coalgebra.comul (R := K) (genericInclusion a) =
      tensorToGeneric (R := R) (K := K) (Coalgebra.comul (R := R) a) := by
  change Coalgebra.comul (R := K) (1 ⊗ₜ[R] a) = _
  rw [TensorProduct.comul_tmul, Bialgebra.comul_one]
  generalize Coalgebra.comul (R := R) a = z
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp [tensorToGeneric, genericInclusion, Algebra.TensorProduct.one_def]
  | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
lemma antipode_genericInclusion (a : A) :
    HopfAlgebra.antipode K (genericInclusion a) =
      genericInclusion (R := R) (K := K) (HopfAlgebra.antipode R a) := by
  simp [genericInclusion, Algebra.TensorProduct.includeRight_apply,
    TensorProduct.antipode_def]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
lemma counit_genericInclusion (a : A) :
    Coalgebra.counit (R := K) (genericInclusion (R := R) (K := K) a) =
      algebraMap R K (Coalgebra.counit (R := R) a) := by
  simp [genericInclusion, Algebra.TensorProduct.includeRight_apply,
    Algebra.smul_def]

noncomputable def closureTensorEmbedding (I : Ideal (K ⊗[R] A)) :
    ((A ⧸ closureIdeal I) ⊗[R] (A ⧸ closureIdeal I)) →ₗ[R]
      (((K ⊗[R] A) ⧸ I) ⊗[K] ((K ⊗[R] A) ⧸ I)) :=
  ((IsLocalization.moduleTensorEquiv R⁰ K
    ((K ⊗[R] A) ⧸ I) ((K ⊗[R] A) ⧸ I)).symm.toLinearMap.restrictScalars R).comp
      (TensorProduct.map (closureEmbedding I).toLinearMap (closureEmbedding I).toLinearMap)

lemma closureTensorEmbedding_injective (I : Ideal (K ⊗[R] A)) :
    Function.Injective (closureTensorEmbedding I) := by
  have := closure_flat I
  exact (IsLocalization.moduleTensorEquiv R⁰ K
    ((K ⊗[R] A) ⧸ I) ((K ⊗[R] A) ⧸ I)).symm.injective.comp
      (TensorProduct.map_injective_of_flat_flat_of_isDomain
        (closureEmbedding I).toLinearMap (closureEmbedding I).toLinearMap
        (closureEmbedding_injective I) (closureEmbedding_injective I))

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma closureTensorEmbedding_comul (I : Ideal (K ⊗[R] A)) (a : A) :
    closureTensorEmbedding I
      (TensorProduct.map (closureIdeal I |>.restrictScalars R).mkQ
        (closureIdeal I |>.restrictScalars R).mkQ (Coalgebra.comul a)) =
    TensorProduct.map (I.restrictScalars K).mkQ (I.restrictScalars K).mkQ
      (Coalgebra.comul (R := K) (genericInclusion a)) := by
  rw [comul_genericInclusion]
  have h : (closureTensorEmbedding I).comp
      (TensorProduct.map (closureIdeal I |>.restrictScalars R).mkQ
        (closureIdeal I |>.restrictScalars R).mkQ) =
      ((TensorProduct.map (I.restrictScalars K).mkQ
        (I.restrictScalars K).mkQ).restrictScalars R).comp tensorToGeneric := by
    ext x y
    rfl
  exact LinearMap.congr_fun h (Coalgebra.comul a)

lemma closure_hopfIdeal (I : Ideal (K ⊗[R] A)) [Ideal.IsHopfIdeal K I] :
    Ideal.IsHopfIdeal R (closureIdeal I) where
  counit_eq_zero {a} ha := by
    apply IsFractionRing.injective R K
    rw [map_zero, ← counit_genericInclusion]
    exact Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars K) ha
  map_mkQ_comul_eq_zero {a} ha := by
    apply closureTensorEmbedding_injective I
    exact (closureTensorEmbedding_comul I a).trans
      ((Submodule.IsCoideal.map_mkQ_comul_eq_zero
        (I := I.restrictScalars K) ha).trans (map_zero (closureTensorEmbedding I)).symm)
  antipode_mem {a} ha := by
    change genericInclusion (HopfAlgebra.antipode R a) ∈ I
    rw [← antipode_genericInclusion]
    exact Ideal.IsHopfIdeal.antipode_mem (R := K) ha

/-- The closure of a closed generic subgroup is a finite flat subgroup,
with the same generic fiber and scheme-theoretic order. -/
theorem finite_flat_closure_of_generic_subgroup
    [Module.Finite R A] [Module.Flat R A]
    (I : Ideal (K ⊗[R] A))
    [Ideal.IsHopfIdeal K I] :
    let ι : A →+* (K ⊗[R] A) :=
      (Algebra.TensorProduct.includeRight :
        A →ₐ[R] (K ⊗[R] A)).toRingHom
    let J : Ideal A := Ideal.comap ι I
    Ideal.IsHopfIdeal R J ∧
      Module.Finite R (A ⧸ J) ∧
      Module.Flat R (A ⧸ J) ∧
      Ideal.map ι J = I ∧
      Module.finrank R (A ⧸ J) =
        Module.finrank K ((K ⊗[R] A) ⧸ I) := by
  exact ⟨closure_hopfIdeal I, inferInstance, closure_flat I,
    closure_generic_fiber I, closure_rank I⟩

end OAI.AlgebraicGeometry.GroupSchemes.SchematicClosure
