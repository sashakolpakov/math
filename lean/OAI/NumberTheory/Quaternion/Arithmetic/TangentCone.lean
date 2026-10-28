import OAI.NumberTheory.Quaternion.Arithmetic.Closure

/-! # Tangent Cone -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.TangentCone

noncomputable section

section

/-! Nonzero tangent directions for nondiscrete matrix subgroups over a
locally compact valued field. Tangent cones here are Mathlib's actual
limits of rescaled displacements, rather than assumed Lie algebras. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open Set Filter _root_.Topology

theorem subgroup_accPt_one_of_not_discrete
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    (H : Subgroup L) (hd : ¬ IsDiscrete (H : Set L)) :
    AccPt (1 : L) (𝓟 (H : Set L)) := by
  by_contra hacc
  rw [accPt_iff_nhds] at hacc
  push Not at hacc
  obtain ⟨U, hU, hisolated⟩ := hacc
  obtain ⟨V, hVU, hV, hV1⟩ := mem_nhds_iff.mp hU
  have he : (Subtype.val ⁻¹' V : Set H) = {1} := by
    ext x
    constructor
    · intro hx
      apply mem_singleton_iff.mpr
      apply Subtype.ext
      exact hisolated x.val ⟨hVU hx, x.property⟩
    · rintro rfl
      exact hV1
  have ho : IsOpen ({1} : Set H) := he ▸ hV.preimage continuous_subtype_val
  have : DiscreteTopology H := discreteTopology_iff_isOpen_singleton_one.mpr ho
  exact hd (isDiscrete_iff_discreteTopology.mpr this)

theorem accPt_image_of_injective_continuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (hinj : Function.Injective f)
    {s : Set X} {x : X} (h : AccPt x (𝓟 s)) : AccPt (f x) (𝓟 (f '' s)) := by
  apply accPt_iff_nhds.mpr
  intro U hU
  obtain ⟨y, ⟨hyU, hys⟩, hyx⟩ := accPt_iff_nhds.mp h _ (hf.continuousAt.preimage_mem_nhds hU)
  exact ⟨f y, ⟨hyU, ⟨y, hys, rfl⟩⟩, fun he => hyx (hinj he)⟩

def matrixTangentCone {F K : Type} [Field F] [Field K] [TopologicalSpace K]
    {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K) (H : Subgroup (G.Points ι)) :
    Set (Matrix (Fin n) (Fin n) K) :=
  tangentConeAt K
    ((fun g : G.Points ι => (g.val : Matrix (Fin n) (Fin n) K)) '' (H : Set (G.Points ι))) 1

def matrixTangentSpan {F K : Type} [Field F] [Field K] [TopologicalSpace K]
    {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K) (H : Subgroup (G.Points ι)) :
    Submodule K (Matrix (Fin n) (Fin n) K) := Submodule.span K (matrixTangentCone G ι H)

/-- Nondiscreteness supplies a nonzero limit of rescaled matrix
displacements at the identity. -/
theorem matrixTangentCone_nonzero
    {F K : Type} [Field F] [NontriviallyNormedField K] [ProperSpace K]
    {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K) (H : Subgroup (G.Points ι))
    (hd : ¬ IsDiscrete (H : Set (G.Points ι))) :
    ∃ X ∈ matrixTangentCone G ι H, X ≠ 0 := by
  let : ProperSpace (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (ProperSpace (Fin n → Fin n → K))
  have hacc := accPt_image_of_injective_continuous
    (fun g : G.Points ι => (g.val : Matrix (Fin n) (Fin n) K))
    (G.points_isClosedEmbedding ι).continuous (G.points_isClosedEmbedding ι).injective
    (subgroup_accPt_one_of_not_discrete H hd)
  have hacc' : AccPt (1 : Matrix (Fin n) (Fin n) K)
      (𝓟 ((fun g : G.Points ι => (g.val : Matrix (Fin n) (Fin n) K)) ''
        (H : Set (G.Points ι)))) := by
    simpa only [OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one] using hacc
  obtain ⟨X, hX, hne⟩ := tangentConeAt_nonempty_of_properSpace (𝕜 := K) hacc'
  exact ⟨X, hX, hne⟩

theorem matrixTangentSpan_nonzero
    {F K : Type} [Field F] [NontriviallyNormedField K] [ProperSpace K]
    {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K) (H : Subgroup (G.Points ι))
    (hd : ¬ IsDiscrete (H : Set (G.Points ι))) : matrixTangentSpan G ι H ≠ ⊥ := by
  obtain ⟨X, hX, hne⟩ := matrixTangentCone_nonzero G ι H hd
  intro he
  have hm : X ∈ matrixTangentSpan G ι H := Submodule.subset_span hX
  rw [he, Submodule.mem_bot] at hm
  exact hne hm

theorem matrixTangentCone_closures_eq_of_commensurable
    {F K : Type} [Field F] [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)
    {H J : Subgroup (G.Points ι)} (h : H.Commensurable J) :
    matrixTangentCone G ι H.topologicalClosure = matrixTangentCone G ι J.topologicalClosure := by
  let f := fun g : G.Points ι => (g.val : Matrix (Fin n) (Fin n) K)
  have hf := (G.points_isClosedEmbedding ι).isEmbedding
  have hn := congrArg (Filter.map f) (ClosureCommensurability.commensurable_closures_nhdsWithin_eq h)
  rw [hf.map_nhdsWithin_eq, hf.map_nhdsWithin_eq] at hn
  have ht := tangentConeAt_congr (𝕜 := K) hn
  simpa only [f, matrixTangentCone, OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one] using ht

end

/-! Conjugation acts linearly on matrix displacements and preserves the
tangent directions of local arithmetic closures. -/

open scoped Classical
open Set Filter _root_.Topology

section

theorem continuousLinearMap_mapsTo_tangentCone
    {K E D : Type*} [Field K] [AddCommGroup E] [AddCommGroup D]
    [Module K E] [Module K D] [TopologicalSpace E] [TopologicalSpace D]
    (f : E →L[K] D) (s : Set E) (x : E) :
    MapsTo f (tangentConeAt K s x) (tangentConeAt K (f '' s) (f x)) := by
  intro y hy
  obtain ⟨α, l, hl, c, d, hd, hs, hcd⟩ := exists_fun_of_mem_tangentConeAt hy
  apply mem_tangentConeAt_of_seq l c (fun a => f (d a))
  · simpa only [Function.comp_def, map_zero] using f.continuous.tendsto 0 |>.comp hd
  · filter_upwards [hs] with a ha
    exact ⟨x + d a, ha, map_add f x (d a)⟩
  · simpa only [Function.comp_def, map_smul] using f.continuous.tendsto y |>.comp hcd

variable {F K : Type} [Field F] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
variable {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)

def matrixConjugation (g : G.Points ι) :
    Matrix (Fin n) (Fin n) K →L[K] Matrix (Fin n) (Fin n) K where
  toFun X := (g.val : Matrix (Fin n) (Fin n) K) * X * ((g⁻¹).val : Matrix (Fin n) (Fin n) K)
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
  cont := (continuous_const.mul continuous_id).mul continuous_const

theorem matrixConjugation_one (g : G.Points ι) : matrixConjugation G ι g 1 = 1 := by
  change (g.val : Matrix (Fin n) (Fin n) K) * 1 *
    ((g⁻¹).val : Matrix (Fin n) (Fin n) K) = 1
  rw [Matrix.mul_one]
  change (((g * g⁻¹).val : ArithmeticGroups.Lattices.Algebraic.SL n K) : Matrix (Fin n) (Fin n) K) = 1
  rw [mul_inv_cancel]
  rfl

theorem matrixConjugation_mapsTo_tangentCone (g : G.Points ι) (H : Subgroup (G.Points ι)) :
    MapsTo (matrixConjugation G ι g) (matrixTangentCone G ι H)
      (matrixTangentCone G ι (H.map (MulAut.conj g).toMonoidHom)) := by
  let e := fun h : G.Points ι => (h.val : Matrix (Fin n) (Fin n) K)
  have himage : matrixConjugation G ι g '' (e '' (H : Set (G.Points ι))) =
      e '' ((H.map (MulAut.conj g).toMonoidHom) : Set (G.Points ι)) := by
    rw [Subgroup.coe_map, image_image, image_image]
    rfl
  have h := continuousLinearMap_mapsTo_tangentCone (matrixConjugation G ι g)
    (e '' (H : Set (G.Points ι))) 1
  rw [himage, matrixConjugation_one] at h
  exact h

theorem closure_map_conj {L : Type*} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] (H : Subgroup L) (g : L) :
    (H.map (MulAut.conj g).toMonoidHom).topologicalClosure =
      H.topologicalClosure.map (MulAut.conj g).toMonoidHom := by
  let e : L ≃ₜ L := (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)
  apply SetLike.coe_injective
  change closure (e '' (H : Set L)) = e '' closure (H : Set L)
  exact (e.image_closure (H : Set L)).symm

variable [T2Space K]

theorem matrixConjugation_preserves_closure_tangentCone
    (g : G.Points ι) (H : Subgroup (G.Points ι))
    (h : (H.map (MulAut.conj g).toMonoidHom).Commensurable H) :
    MapsTo (matrixConjugation G ι g) (matrixTangentCone G ι H.topologicalClosure)
      (matrixTangentCone G ι H.topologicalClosure) := by
  have hm := matrixConjugation_mapsTo_tangentCone G ι g H.topologicalClosure
  rw [← closure_map_conj] at hm
  rw [matrixTangentCone_closures_eq_of_commensurable G ι h] at hm
  exact hm

end

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) (v : LocalAdeles.Place F)

theorem rational_conjugation_preserves_localArithmetic_tangentCone
    (hS : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) (g : G.RationalPoints) :
    MapsTo (matrixConjugation G (LocalAdeles.localEmbedding v) (LocalAdeles.diagonalLocal G v g))
      (matrixTangentCone G (LocalAdeles.localEmbedding v) (Closure.localArithmeticSubgroup G S v).topologicalClosure)
      (matrixTangentCone G (LocalAdeles.localEmbedding v) (Closure.localArithmeticSubgroup G S v).topologicalClosure) := by
  apply matrixConjugation_preserves_closure_tangentCone
  have h := Closure.localArithmetic_conjugate_commensurable G S v hS g⁻¹
  rw [map_inv, Subgroup.comap_equiv_eq_map_symm'] at h
  have he : (MulAut.conj (LocalAdeles.diagonalLocal G v g)⁻¹).symm.toMonoidHom =
      (MulAut.conj (LocalAdeles.diagonalLocal G v g)).toMonoidHom := by
    ext x
    simp
  rwa [he] at h

theorem rational_conjugation_preserves_localArithmetic_tangentSpan
    (hS : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) (g : G.RationalPoints) :
    (matrixTangentSpan G (LocalAdeles.localEmbedding v) (Closure.localArithmeticSubgroup G S v).topologicalClosure).map
        (matrixConjugation G (LocalAdeles.localEmbedding v) (LocalAdeles.diagonalLocal G v g)).toLinearMap ≤
      matrixTangentSpan G (LocalAdeles.localEmbedding v) (Closure.localArithmeticSubgroup G S v).topologicalClosure := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  intro X hX
  exact Submodule.subset_span
    (rational_conjugation_preserves_localArithmetic_tangentCone G S v hS g hX)

end

end OAI.NumberTheory.Quaternion.Arithmetic.TangentCone
