import OAI.Geometry.ComplexBall.Archimedean
import OAI.Geometry.ComplexBall.Congruence

/-! # Arithmetic Presentation -/

namespace OAI.Geometry.ComplexBall.ArithmeticPresentation.Quotient

noncomputable section

/-! The actual arithmetic presentation: one distinguished completed factor,
the original integral stabilizer, and compactness of every omitted factor. -/

open scoped Classical
open _root_.NumberField _root_.Topology

section Points
variable {k K : Type} [Field k] [Field K] {n : ℕ}
    [TopologicalSpace K]

def matrixPointsCongr (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) (ι κ : k →+* K) (h : ι = κ) :
    G.Points ι ≃ₜ* G.Points κ where
  toFun g := ⟨g.val, h ▸ g.property⟩
  invFun g := ⟨g.val, h.symm ▸ g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

end Points

section SinglePlace
variable {k : Type} [Field k] [NumberField k] {n : ℕ}

def completedRealPointsEquiv (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) (v : InfinitePlace k) (hv : v.IsReal) :
    G.AtPlace v ≃ₜ* G.Points (v.embedding_of_isReal hv) :=
  (G.pointsContinuousMulEquiv (algebraMap k v.Completion)
    (InfinitePlace.Completion.ringEquivRealOfIsReal hv)
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous).trans
      (matrixPointsCongr _ _ _ (NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup.realPlaceEmbedding_eq v hv))

omit [NumberField k] in
lemma completedRealPointsEquiv_entry (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n)
    (v : InfinitePlace k) (hv : v.IsReal) (g : G.AtPlace v) (i j : Fin n) :
    (completedRealPointsEquiv G v hv g).val i j =
      InfinitePlace.Completion.ringEquivRealOfIsReal hv (g.val i j) := rfl

def singlePlaceProductEquiv (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) (v : InfinitePlace k) :
    G.AtPlace v ≃ₜ* G.ArchimedeanProduct {v} where
  toFun g w := (Set.mem_singleton_iff.mp w.property).symm ▸ g
  invFun g := g ⟨v, Set.mem_singleton v⟩
  left_inv _ := rfl
  right_inv g := by
    funext w
    obtain ⟨w, hw⟩ := w
    have he : w = v := hw
    subst w
    rfl
  map_mul' g h := by
    funext w
    obtain ⟨w, hw⟩ := w
    have he : w = v := hw
    subst w
    rfl
  continuous_toFun := by
    apply continuous_pi
    intro w
    obtain ⟨w, hw⟩ := w
    have he : w = v := hw
    subst w
    exact continuous_id
  continuous_invFun := continuous_apply _

end SinglePlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
lemma realPlaceEmbedding_eq_realEmbedding (μ : E →+* ℂ) :
    (RealPlaces.ArithmeticQuotient.realPlace μ).embedding_of_isReal (IsTotallyReal.isReal _) = RealPlaces.ArithmeticQuotient.realEmbedding μ := by
  have hreal : ComplexEmbedding.IsReal (Complex.ofRealHom.comp (RealPlaces.ArithmeticQuotient.realEmbedding μ)) := by
    ext x
    change star (RealPlaces.ArithmeticQuotient.realEmbedding μ x : ℂ) = (RealPlaces.ArithmeticQuotient.realEmbedding μ x : ℂ)
    simp
  ext x
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply]
  change (InfinitePlace.mk (Complex.ofRealHom.comp (RealPlaces.ArithmeticQuotient.realEmbedding μ))).embedding x = _
  rw [InfinitePlace.embedding_mk_eq_of_isReal hreal]
  rfl

def originalAtDistinguishedPlaceEquiv (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) (μ : E →+* ℂ) :
    (ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ).AtPlace (RealPlaces.ArithmeticQuotient.realPlace μ) ≃ₜ* ArithmeticQuotientEquationsData.ArchimedeanSU b μ :=
  (completedRealPointsEquiv (ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ) (RealPlaces.ArithmeticQuotient.realPlace μ)
    (IsTotallyReal.isReal _)).trans
      ((matrixPointsCongr _ _ _ (realPlaceEmbedding_eq_realEmbedding μ)).trans
        (Archimedean.ArithmeticQuotient.originalRealPointsEquiv b hb δ hδ hδ0 μ))

def originalArchimedeanProductEquiv (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) (μ : E →+* ℂ) :
    ArithmeticQuotientEquationsData.ArchimedeanSU b μ ≃ₜ*
      (ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ).ArchimedeanProduct {RealPlaces.ArithmeticQuotient.realPlace μ} :=
  (originalAtDistinguishedPlaceEquiv b hb δ hδ hδ0 μ).symm.trans
    (singlePlaceProductEquiv _ (RealPlaces.ArithmeticQuotient.realPlace μ))

lemma originalAtDistinguishedPlaceEquiv_diagonal (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) (μ : E →+* ℂ)
    (g : ArithmeticQuotientEquationsData.RationalSU b) :
    originalAtDistinguishedPlaceEquiv b hb δ hδ hδ0 μ
      ((ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ).diagonalAtPlace (RealPlaces.ArithmeticQuotient.realPlace μ)
        (ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0 g)) = ArithmeticQuotientEquationsData.infinitePlaceMap b μ g := by
  let G := ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ
  let w := RealPlaces.ArithmeticQuotient.realPlace μ
  let hv := IsTotallyReal.isReal w
  have he : matrixPointsCongr G _ _ (realPlaceEmbedding_eq_realEmbedding μ)
      (completedRealPointsEquiv G w hv (G.diagonalAtPlace w
        (ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0 g))) =
      G.map (RingHom.id _) (RealPlaces.ArithmeticQuotient.realEmbedding μ) (ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0 g) := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change InfinitePlace.Completion.ringEquivRealOfIsReal hv
      (algebraMap (ArithmeticQuotientEquationsData.RealField E) w.Completion
        ((ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0 g).val i j)) = _
    have hx := RingHom.congr_fun (NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup.realPlaceEmbedding_eq w hv)
      ((ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0 g).val i j)
    change _ = w.embedding_of_isReal hv _ at hx
    rw [realPlaceEmbedding_eq_realEmbedding μ] at hx
    exact hx
  exact (congrArg (Archimedean.ArithmeticQuotient.originalRealPointsEquiv b hb δ hδ hδ0 μ) he).trans
    (Archimedean.ArithmeticQuotient.originalRealPointsEquiv_diagonal b hb δ hδ hδ0 μ g)

lemma originalArchimedeanProductEquiv_diagonal (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) (μ : E →+* ℂ)
    (g : ArithmeticQuotientEquationsData.RationalSU b) :
    originalArchimedeanProductEquiv b hb δ hδ hδ0 μ (ArithmeticQuotientEquationsData.infinitePlaceMap b μ g) =
      (ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ).diagonal {RealPlaces.ArithmeticQuotient.realPlace μ}
        (ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0 g) := by
  funext w
  obtain ⟨w, hw⟩ := w
  have he : w = RealPlaces.ArithmeticQuotient.realPlace μ := hw
  subst w
  change (originalAtDistinguishedPlaceEquiv b hb δ hδ hδ0 μ).symm (ArithmeticQuotientEquationsData.infinitePlaceMap b μ g) = _
  apply (originalAtDistinguishedPlaceEquiv b hb δ hδ hδ0 μ).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact (originalAtDistinguishedPlaceEquiv_diagonal b hb δ hδ hδ0 μ g).symm

theorem originalUnitary_arithmeticPresentation (b : E) (hb : IsCMField.complexConj E b = b)
    (hb0 : b ≠ 0) (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (μ : E →+* ℂ)
    (hpos : ∀ ν : E →+* ℂ, ν ≠ μ → ν ≠ (starRingEnd ℂ).comp μ → 0 < (ν b).re) :
    NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.IsArithmeticPresentation (Connected.ArithmeticQuotient.originalConnectedSemisimpleUnitaryGroup b hb hb0 δ hδ hδ0)
      (ArithmeticQuotientEquationsData.infinitePlaceMap b μ) (Congruence.ArithmeticQuotient.integralUnitarySubgroup b) := by
  refine ⟨IntegralLattice.ArithmeticQuotient.cmIntegralLattice δ hδ hδ0, ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0,
    {RealPlaces.ArithmeticQuotient.realPlace μ}, originalArchimedeanProductEquiv b hb δ hδ hδ0 μ, ?_, ?_, ?_⟩
  · intro v hv
    exact RealPlaces.ArithmeticQuotient.originalUnitary_omittedPlace_compact b hb δ hδ hδ0 μ hpos v hv
  · exact Congruence.ArithmeticQuotient.integralUnitary_map_stabilizer b hb δ hδ hδ0
  · exact originalArchimedeanProductEquiv_diagonal b hb δ hδ hδ0 μ

end

end OAI.Geometry.ComplexBall.ArithmeticPresentation.Quotient
