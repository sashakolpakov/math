import OAI.AlgebraicGeometry.Comparison.Betti.ParameterFinCoordinateGerms

/-! # Normal Slice -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.NormalSlice.AnalyticLocal

noncomputable section

section

/-! Restricting several normal coordinates defines the actual slice map on holomorphic germs. -/

open Set Filter
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def normalSliceEvaluation {n : ℕ} (x : E) (z : Fin n → ℂ) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, z) →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x :=
  Holomorphic.GermMaps.AnalyticLocal.holomorphicComposition (fun y : E => (y, z)) (differentiable_id.prodMk (differentiable_const z)) x

def normalParameterInclusion {n : ℕ} (x : E) (z : Fin n → ℂ) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, z) :=
  Holomorphic.GermMaps.AnalyticLocal.holomorphicComposition Prod.fst differentiable_fst (x, z)

def normalCoordinateGerm {n : ℕ} (x : E) (z : Fin n → ℂ) (i : Fin n) : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, z) :=
  ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction (x, z) (fun p : E × (Fin n → ℂ) => p.2 i - z i) isOpen_univ (mem_univ _)
    (by
      have hv : Differentiable ℂ (fun p : E × (Fin n → ℂ) => p.2 i) :=
        (show Differentiable ℂ (fun z : Fin n → ℂ => z i) from differentiable_apply i).comp
          (show Differentiable ℂ (Prod.snd : E × (Fin n → ℂ) → (Fin n → ℂ)) from differentiable_snd)
      exact (hv.sub_const (z i)).differentiableOn)

theorem normalCoordinateGerm_val {n : ℕ} (x : E) (z : Fin n → ℂ) (i : Fin n) :
    (normalCoordinateGerm x z i).val =
      ((fun p : E × (Fin n → ℂ) => p.2 i - z i) : Germ (𝓝 (x, z)) ℂ) := rfl

theorem normalSliceEvaluation_parameterInclusion {n : ℕ} (x : E) (z : Fin n → ℂ) :
    (normalSliceEvaluation x z).comp (normalParameterInclusion x z) = RingHom.id _ := by
  rw [normalSliceEvaluation, normalParameterInclusion, Holomorphic.GermMaps.AnalyticLocal.holomorphicComposition_comp]
  exact Holomorphic.GermMaps.AnalyticLocal.holomorphicComposition_id x

theorem normalSliceEvaluation_coordinate {n : ℕ} (x : E) (z : Fin n → ℂ) (i : Fin n) :
    normalSliceEvaluation x z (normalCoordinateGerm x z i) = 0 := by
  apply Subtype.ext
  change ((fun _ : E => z i - z i) : Germ (𝓝 x) ℂ) = 0
  simp only [sub_self]
  rfl

theorem normalParameterInclusion_slice_zero (x : E) (z : Fin 0 → ℂ) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, z)) :
    normalParameterInclusion x z (normalSliceEvaluation x z a) = a := by
  obtain ⟨v, hva, _⟩ := a.property
  apply Subtype.ext
  change GermComposition.AnalyticLocal.germComposition Prod.fst _ (GermComposition.AnalyticLocal.germComposition (fun y : E => (y, z)) _ a.val) = a.val
  rw [← hva]
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall (fun p => congrArg v (show (p.1, z) = p from by
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _))

theorem normalSliceEvaluation_zero_eq_zero (x : E) (z : Fin 0 → ℂ) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, z))
    (ha : normalSliceEvaluation x z a = 0) : a = 0 :=
  (normalParameterInclusion_slice_zero x z a).symm.trans
    ((congrArg (normalParameterInclusion x z) ha).trans (map_zero _))

end

section

/-! The actual normal-coordinate splitting preserves coordinate germs and restriction to the full slice. -/

open Set Filter
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem parameterFinCoordinateGermEquiv_representative (n : ℕ) (x : E) (z : Fin (n + 1) → ℂ)
    (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, z)) (v : E × (Fin (n + 1) → ℂ) → ℂ)
    (ha : a.val = (v : Germ (𝓝 (x, z)) ℂ)) :
    (ParameterFinCoordinateGerms.AnalyticLocal.parameterFinCoordinateGermEquiv E n x z a).val =
      ((fun p : (E × (Fin n → ℂ)) × ℂ => v (p.1.1, Fin.cases p.2 p.1.2)) :
        Germ (𝓝 ((x, fun i : Fin n => z i.succ), z 0)) ℂ) := by
  let L := ParameterFinCoordinateGerms.AnalyticLocal.parameterFinCoordinateEquiv E n
  change (GermCoordinateEquiv.AnalyticLocal.holomorphicPullbackAt L.symm L.symm.differentiable (L (x, z)) (x, z)
    (L.symm_apply_apply (x, z)) a).val = _
  rw [GermCoordinateEquiv.AnalyticLocal.holomorphicPullbackAt_val, ha]
  rfl

theorem parameterFinCoordinateGermEquiv_normal_zero (n : ℕ) (x : E) (z : Fin (n + 1) → ℂ) :
    ParameterFinCoordinateGerms.AnalyticLocal.parameterFinCoordinateGermEquiv E n x z (normalCoordinateGerm x z 0) =
      GermPolynomialNe.AnalyticLocal.centeredCoordinateGerm (x, fun i : Fin n => z i.succ) (z 0) := by
  apply Subtype.ext
  exact parameterFinCoordinateGermEquiv_representative n x z (normalCoordinateGerm x z 0)
    (fun p => p.2 0 - z 0) (normalCoordinateGerm_val x z 0)

theorem parameterFinCoordinateGermEquiv_normal_succ (n : ℕ) (x : E) (z : Fin (n + 1) → ℂ) (i : Fin n) :
    ParameterFinCoordinateGerms.AnalyticLocal.parameterFinCoordinateGermEquiv E n x z (normalCoordinateGerm x z i.succ) =
      GermPolynomialNe.AnalyticLocal.parameterInclusion (x, fun j : Fin n => z j.succ) (z 0)
        (normalCoordinateGerm x (fun j : Fin n => z j.succ) i) := by
  apply Subtype.ext
  exact parameterFinCoordinateGermEquiv_representative n x z (normalCoordinateGerm x z i.succ)
    (fun p => p.2 i.succ - z i.succ) (normalCoordinateGerm_val x z i.succ)

theorem normalSliceEvaluation_split (n : ℕ) (x : E) (z : Fin (n + 1) → ℂ) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, z)) :
    normalSliceEvaluation x (fun i : Fin n => z i.succ)
      (GermPolynomialNe.AnalyticLocal.sliceEvaluation (x, fun i : Fin n => z i.succ) (z 0) (ParameterFinCoordinateGerms.AnalyticLocal.parameterFinCoordinateGermEquiv E n x z a)) =
        normalSliceEvaluation x z a := by
  obtain ⟨v, hva, _⟩ := a.property
  have hs := parameterFinCoordinateGermEquiv_representative n x z a v hva.symm
  apply Subtype.ext
  change GermComposition.AnalyticLocal.germComposition (fun y : E => (y, fun i : Fin n => z i.succ)) _
    (GermComposition.AnalyticLocal.germComposition (fun p : E × (Fin n → ℂ) => (p, z 0)) _
      (ParameterFinCoordinateGerms.AnalyticLocal.parameterFinCoordinateGermEquiv E n x z a).val) =
    GermComposition.AnalyticLocal.germComposition (fun y : E => (y, z)) _ a.val
  rw [hs, ← hva]
  apply Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro y
  apply congrArg v
  apply Prod.ext
  · rfl
  · funext i
    exact Fin.cases rfl (fun _ => rfl) i

end

/-! The kernel of restriction to a finite coordinate slice is generated by its actual normal coordinate germs. -/

open Set Filter
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem normalSlice_zero_mem_ideal (n : ℕ) :
    ∀ (x : E) (z : Fin n → ℂ) (J : Ideal (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, z))),
      (∀ i, normalCoordinateGerm x z i ∈ J) →
        ∀ a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, z), normalSliceEvaluation x z a = 0 → a ∈ J := by
  induction n with
  | zero =>
      intro x z J _ a ha
      rw [normalSliceEvaluation_zero_eq_zero x z a ha]
      exact J.zero_mem
  | succ n ih =>
      intro x z J hJ a ha
      let z' : Fin n → ℂ := fun i => z i.succ
      let e := ParameterFinCoordinateGerms.AnalyticLocal.parameterFinCoordinateGermEquiv E n x z
      let J' := Ideal.map e.toRingHom J
      let p := GermPolynomialNe.AnalyticLocal.parameterInclusion (x, z') (z 0)
      let I := Ideal.comap p J'
      have hzero : GermPolynomialNe.AnalyticLocal.centeredCoordinateGerm (x, z') (z 0) ∈ J' := by
        have h := Ideal.mem_map_of_mem e.toRingHom (hJ 0)
        change ParameterFinCoordinateGerms.AnalyticLocal.parameterFinCoordinateGermEquiv E n x z (normalCoordinateGerm x z 0) ∈ J' at h
        rw [parameterFinCoordinateGermEquiv_normal_zero] at h
        exact h
      have hI (i : Fin n) : normalCoordinateGerm x z' i ∈ I := by
        have h := Ideal.mem_map_of_mem e.toRingHom (hJ i.succ)
        change ParameterFinCoordinateGerms.AnalyticLocal.parameterFinCoordinateGermEquiv E n x z (normalCoordinateGerm x z i.succ) ∈ J' at h
        rw [parameterFinCoordinateGermEquiv_normal_succ] at h
        exact h
      have hs : normalSliceEvaluation x z' (GermPolynomialNe.AnalyticLocal.sliceEvaluation (x, z') (z 0) (e a)) = 0 :=
        (normalSliceEvaluation_split n x z a).trans ha
      have hparam : p (GermPolynomialNe.AnalyticLocal.sliceEvaluation (x, z') (z 0) (e a)) ∈ J' :=
        ih x z' I hI _ hs
      have hea : e a ∈ J' := by
        obtain ⟨b, hb⟩ := GermSliceDivision.AnalyticLocal.germ_coordinate_division (x, z') (z 0) (e a)
        rw [hb]
        exact J'.add_mem hparam (J'.mul_mem_right b hzero)
      obtain ⟨b, hb, hba⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hea
      exact e.injective hba ▸ hb

theorem normalSliceEvaluation_ker (n : ℕ) (x : E) (z : Fin n → ℂ) :
    RingHom.ker (normalSliceEvaluation x z) = Ideal.span (Set.range (normalCoordinateGerm x z)) := by
  apply le_antisymm
  · intro a ha
    exact normalSlice_zero_mem_ideal n x z (Ideal.span (Set.range (normalCoordinateGerm x z)))
      (fun i => Ideal.subset_span ⟨i, rfl⟩) a ha
  · apply Ideal.span_le.mpr
    rintro a ⟨i, rfl⟩
    exact normalSliceEvaluation_coordinate x z i

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.NormalSlice.AnalyticLocal
