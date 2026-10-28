import OAI.NumberTheory.ArithmeticGroups.Lattices.IntegralLattice

/-! # Realizations -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Polynomial zero sets are closed in archimedean matrix topology. These
lemmas relate the algebraic presentation to its actual topological groups. -/

open scoped Classical
open _root_.Topology

section

variable {k K : Type} [Field k] [Field K] {n : ℕ}
variable (G : Algebraic.MatrixAlgebraicGroup k n) (ι : k →+* K)
variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

omit [T2Space K] in
theorem Algebraic.MatrixAlgebraicGroup.continuous_evaluateMatrix (p : Algebraic.CoordinatePolynomial n k) :
    Continuous (fun g : Algebraic.SL n K => Algebraic.evaluateMatrix ι g p) := by
  have h : Continuous (fun g : Algebraic.SL n K => fun ij : Fin n × Fin n => g ij.1 ij.2) := by
    fun_prop
  convert (MvPolynomial.continuous_eval (MvPolynomial.map ι p)).comp h using 1
  ext g
  simp only [Function.comp_apply, Algebraic.evaluateMatrix, MvPolynomial.eval_map]
  rfl

theorem Algebraic.MatrixAlgebraicGroup.subgroup_isClosed : IsClosed (G.subgroup K ι : Set (Algebraic.SL n K)) := by
  have he : (G.subgroup K ι : Set (Algebraic.SL n K)) =
      ⋂ p ∈ G.equations, {g : Algebraic.SL n K | Algebraic.evaluateMatrix ι g p = 0} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    exact G.mem_iff K ι g
  rw [he]
  apply isClosed_iInter
  intro p
  apply isClosed_iInter
  intro _
  exact isClosed_eq (Algebraic.MatrixAlgebraicGroup.continuous_evaluateMatrix ι p) continuous_const

theorem Algebraic.MatrixAlgebraicGroup.points_isClosedEmbedding :
    IsClosedEmbedding (fun g : G.Points ι => (g.val : Matrix (Fin n) (Fin n) K)) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.comp
    (G.subgroup_isClosed ι).isClosedEmbedding_subtypeVal

instance Algebraic.MatrixAlgebraicGroup.pointsLocallyCompact [LocallyCompactSpace K] : LocallyCompactSpace (G.Points ι) := by
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → K))
  exact (G.points_isClosedEmbedding ι).locallyCompactSpace

instance Algebraic.MatrixAlgebraicGroup.pointsSecondCountable [SecondCountableTopology K] :
    SecondCountableTopology (G.Points ι) := by
  let : SecondCountableTopology (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → K))
  exact (G.points_isClosedEmbedding ι).isEmbedding.secondCountableTopology

omit [IsTopologicalRing K] [T2Space K] in
theorem Algebraic.MatrixAlgebraicGroup.continuous_map {L : Type} [Field L] [TopologicalSpace L]
    (f : K →+* L) (hf : Continuous f) : Continuous (G.map ι f) := by
  exact IsInducing.subtypeVal.continuous_iff.mpr
    (hf.specialLinearGroup_map.comp continuous_subtype_val)

/-- Scalar extension along an isomorphism of fields is an isomorphism of
the actual polynomial point groups. -/
def Algebraic.MatrixAlgebraicGroup.pointsEquiv {L : Type} [Field L] (e : K ≃+* L) :
    G.Points ι ≃* G.Points (e.toRingHom.comp ι) where
  toFun := G.map ι e.toRingHom
  invFun g := ⟨Matrix.SpecialLinearGroup.map e.symm.toRingHom g.val, by
    apply (G.mem_iff K ι _).mpr
    intro p hp
    apply e.injective
    change e.toRingHom (Algebraic.evaluateMatrix ι
      (Matrix.SpecialLinearGroup.map e.symm.toRingHom g.val) p) = e.toRingHom 0
    have h := (G.mem_iff L (e.toRingHom.comp ι) g.val).mp g.property p hp
    simpa only [Algebraic.evaluateMatrix, MvPolynomial.map_eval₂Hom,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, RingEquiv.toRingHom_apply_symm_toRingHom_apply,
      map_zero] using h⟩
  left_inv g := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact e.symm_apply_apply (g.val i j)
  right_inv g := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact e.apply_symm_apply (g.val i j)
  map_mul' := map_mul (G.map ι e.toRingHom)

/-- A topological field isomorphism induces a topological group isomorphism. -/
def Algebraic.MatrixAlgebraicGroup.pointsContinuousMulEquiv {L : Type} [Field L] [TopologicalSpace L]
    (e : K ≃+* L) (he : Continuous e) (he' : Continuous e.symm) :
    G.Points ι ≃ₜ* G.Points (e.toRingHom.comp ι) where
  toMulEquiv := G.pointsEquiv ι e
  continuous_toFun := G.continuous_map ι e.toRingHom he
  continuous_invFun := IsInducing.subtypeVal.continuous_iff.mpr
    (he'.specialLinearGroup_map.comp continuous_subtype_val)

end

variable {k : Type} [Field k] [NumberField k] {n : ℕ}
variable (G : Algebraic.MatrixAlgebraicGroup k n)

omit [NumberField k] in
theorem Algebraic.MatrixAlgebraicGroup.realPlaceEmbedding_eq (v : NumberField.InfinitePlace k) (hv : v.IsReal) :
    (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).toRingHom.comp
        (algebraMap k v.Completion) = v.embedding_of_isReal hv := by
  ext x
  exact NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv
    ((WithAbs.equiv v.val).symm x)

/-- The completion at a real place gives the same topological point group
as extension along its real embedding. -/
def Algebraic.MatrixAlgebraicGroup.realPlaceEquiv (v : NumberField.InfinitePlace k) (hv : v.IsReal) :
    G.AtPlace v ≃ₜ* G.Points (v.embedding_of_isReal hv) := by
  rw [← Algebraic.MatrixAlgebraicGroup.realPlaceEmbedding_eq v hv]
  exact G.pointsContinuousMulEquiv (algebraMap k v.Completion)
    (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv)
    (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
    (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
