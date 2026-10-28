import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ArithmeticCompactness
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ArchimedeanModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DefiniteUnitaryCompactness

/-! # Archimedean Compactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ArchimedeanCompactness.HermitianArithmetic

noncomputable section

/-! Projection to the specified complex embedding preserves compactness
of the original principal quotient. Definite omitted factors make that
projection closed, so the projected principal subgroup is also discrete. -/

open _root_.NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem complexForm_pairing (H : Matrix (Fin 3) (Fin 3) E) (μ : E →+* ℂ)
    (x y : Fin 3 → ℂ) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (H.transpose.map μ) x y =
      Datum.RankThreePELDatum.complexMatrixHermitian μ H y x := by
  rw [DefiniteUnitaryCompactness.formValue_linearFirst, Matrix.transpose_map, Matrix.transpose_transpose,
    ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply]
  rfl

theorem complexForm_hermitian (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = IsCMField.complexConj E (H j i)) (μ : E →+* ℂ) :
    (H.transpose.map μ).conjTranspose = H.transpose.map μ := by
  ext i j
  change star (μ (H i j)) = μ (H j i)
  exact (IsCMField.complexEmbedding_complexConj E μ (H i j)).symm.trans
    (congrArg μ (hH j i).symm)

theorem complex_definite_compact (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = IsCMField.complexConj E (H j i)) (μ : E →+* ℂ)
    (hdef : (∀ x : Fin 3 → ℂ, x ≠ 0 →
      0 < (Datum.RankThreePELDatum.complexMatrixHermitian μ H x x).re) ∨
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        (Datum.RankThreePELDatum.complexMatrixHermitian μ H x x).re < 0)) :
    CompactSpace (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.transpose.map μ)) := by
  apply DefiniteUnitaryCompactness.complex_specialUnitary_compact_of_definite _ (complexForm_hermitian H hH μ)
  simpa only [complexForm_pairing] using hdef

variable (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (H : Matrix (Fin 3) (Fin 3) E) (μ : E →+* ℂ)

theorem omittedPlace_compact
    (hH : ∀ i j, H i j = IsCMField.complexConj E (H j i))
    (hdef : ∀ ν : E →+* ℂ, ν ≠ μ → ν ≠ (starRingEnd ℂ).comp μ →
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        0 < (Datum.RankThreePELDatum.complexMatrixHermitian ν H x x).re) ∨
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        (Datum.RankThreePELDatum.complexMatrixHermitian ν H x x).re < 0))
    (v : InfinitePlace (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E)) (hv : v ≠ Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace μ) :
    CompactSpace ((ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H).AtPlace v) := by
  let G := ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H
  have hreal := IsTotallyReal.isReal v
  let α := v.embedding_of_isReal hreal
  let ν := ComplexEmbedding.lift E (Complex.ofRealHom.comp α)
  have he : Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding ν = α := Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding_lift α
  have hα : α ≠ Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ := by
    intro h
    apply hv
    rw [← Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace_embedding v hreal]
    change InfinitePlace.mk (Complex.ofRealHom.comp α) = Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace μ
    rw [h]
    rfl
  have hν : ν ≠ μ := fun h => hα (he.symm.trans (congrArg Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding h))
  have hνc : ν ≠ (starRingEnd ℂ).comp μ := by
    intro h
    exact hα (he.symm.trans ((congrArg Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding h).trans
      (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding_conjugate μ)))
  let : CompactSpace (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.transpose.map ν)) :=
    complex_definite_compact H hH ν (hdef ν hν hνc)
  let e := (Geometry.ComplexBall.ArithmeticPresentation.Quotient.completedRealPointsEquiv G v hreal).trans
    ((Geometry.ComplexBall.ArithmeticPresentation.Quotient.matrixPointsCongr G α (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding ν) he.symm).trans
      (ArchimedeanModel.HermitianArithmetic.realPointsEquiv δ hδ hδ0 H ν))
  exact e.symm.toHomeomorph.compactSpace

def complexProjection :
    (ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H).ArchimedeanProduct Set.univ →*
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.transpose.map μ) :=
  (ArchimedeanModel.HermitianArithmetic.atPlaceEquiv δ hδ hδ0 H μ).toMonoidHom.comp
    ((Geometry.ComplexBall.ArithmeticPresentation.Quotient.singlePlaceProductEquiv (ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H)
      (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace μ)).symm.toMonoidHom.comp
        (NumberTheory.ArithmeticGroups.Lattices.Discrete.Construction.archimedeanProjection (ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H) {Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace μ}))

theorem complexProjection_continuous : Continuous (complexProjection δ hδ hδ0 H μ) :=
  (ArchimedeanModel.HermitianArithmetic.atPlaceEquiv δ hδ hδ0 H μ).continuous.comp
    ((Geometry.ComplexBall.ArithmeticPresentation.Quotient.singlePlaceProductEquiv (ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H)
      (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace μ)).symm.continuous.comp
        (NumberTheory.ArithmeticGroups.Lattices.CompactTransport.Construction.continuous_archimedeanProjection _ _))

theorem complexProjection_surjective : Function.Surjective (complexProjection δ hδ hδ0 H μ) :=
  (ArchimedeanModel.HermitianArithmetic.atPlaceEquiv δ hδ hδ0 H μ).surjective.comp
    ((Geometry.ComplexBall.ArithmeticPresentation.Quotient.singlePlaceProductEquiv (ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H)
      (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace μ)).symm.surjective.comp
        (NumberTheory.ArithmeticGroups.Lattices.CompactTransport.Construction.archimedeanProjection_surjective _ _))

theorem complexProjection_closed
    (hH : ∀ i j, H i j = IsCMField.complexConj E (H j i))
    (hdef : ∀ ν : E →+* ℂ, ν ≠ μ → ν ≠ (starRingEnd ℂ).comp μ →
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        0 < (Datum.RankThreePELDatum.complexMatrixHermitian ν H x x).re) ∨
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        (Datum.RankThreePELDatum.complexMatrixHermitian ν H x x).re < 0)) :
    IsClosedMap (complexProjection δ hδ hδ0 H μ) := by
  have hp := NumberTheory.ArithmeticGroups.Lattices.Discrete.Construction.archimedeanProjection_closed (ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H)
    {Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace μ} (fun v hv => omittedPlace_compact δ hδ hδ0 H μ hH hdef v
      (by simpa only [Set.mem_singleton_iff] using hv))
  exact (ArchimedeanModel.HermitianArithmetic.atPlaceEquiv δ hδ hδ0 H μ).toHomeomorph.isClosedMap.comp
    ((Geometry.ComplexBall.ArithmeticPresentation.Quotient.singlePlaceProductEquiv (ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H)
      (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace μ)).symm.toHomeomorph.isClosedMap.comp hp)

def principalComplexHom (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (N : ℕ) :
    ↥(Groups.principalLatticeSubgroup (R := E) Λ.toAddSubgroup N ⊓
      Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H)) →*
        RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.transpose.map μ) :=
  (ArchimedeanModel.HermitianArithmetic.complexHom δ hδ hδ0 H μ).comp (Subgroup.inclusion inf_le_right)

theorem principalComplexHom_matrix (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (N : ℕ)
    (g : ↥(Groups.principalLatticeSubgroup (R := E) Λ.toAddSubgroup N ⊓
      Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H))) :
    (principalComplexHom δ hδ hδ0 H μ Λ N g).val.val =
      (LinearMap.toMatrix' g.val.toLinearMap).map μ :=
  ArchimedeanModel.HermitianArithmetic.complexHom_matrix δ hδ hδ0 H μ ⟨g.val, g.property.2⟩

theorem complexProjection_principal (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (N : ℕ) :
    (complexProjection δ hδ hδ0 H μ).comp (ArithmeticCompactness.HermitianArithmetic.principalArchimedeanHom δ hδ hδ0 H Λ N) =
      principalComplexHom δ hδ hδ0 H μ Λ N := by
  ext g
  rfl

theorem principal_complex_compact
    (hH : ∀ i j, H i j = IsCMField.complexConj E (H j i)) (hdet : H.det ≠ 0)
    (han : ∀ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Datum.RankThreePELDatum.matrixHermitian H v v = 0 → v = 0)
    (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)
    (N : ℕ) (hN : N ≠ 0) :
    CompactSpace (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.transpose.map μ) ⧸
      (principalComplexHom δ hδ hδ0 H μ Λ N).range) := by
  let : CompactSpace ((ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H).ArchimedeanProduct Set.univ ⧸
      (ArithmeticCompactness.HermitianArithmetic.principalArchimedeanHom δ hδ hδ0 H Λ N).range) :=
    ArithmeticCompactness.HermitianArithmetic.principal_archimedean_compact δ hδ hδ0 H hH hdet han μ Λ hΛ N hN
  have hc := NumberTheory.ArithmeticGroups.Lattices.QuotientMeasure.Construction.compact_quotient_map_of_surjective
    (complexProjection δ hδ hδ0 H μ) (complexProjection_continuous δ hδ hδ0 H μ)
    (complexProjection_surjective δ hδ hδ0 H μ)
    (ArithmeticCompactness.HermitianArithmetic.principalArchimedeanHom δ hδ hδ0 H Λ N).range
  rw [MonoidHom.map_range, complexProjection_principal] at hc
  exact hc

theorem principal_complex_discrete
    (hH : ∀ i j, H i j = IsCMField.complexConj E (H j i)) (hdet : H.det ≠ 0)
    (hdef : ∀ ν : E →+* ℂ, ν ≠ μ → ν ≠ (starRingEnd ℂ).comp μ →
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        0 < (Datum.RankThreePELDatum.complexMatrixHermitian ν H x x).re) ∨
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        (Datum.RankThreePELDatum.complexMatrixHermitian ν H x x).re < 0))
    (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)
    (N : ℕ) (hN : N ≠ 0) :
    DiscreteTopology (principalComplexHom δ hδ hδ0 H μ Λ N).range := by
  let : DiscreteTopology (ArithmeticCompactness.HermitianArithmetic.principalArchimedeanHom δ hδ hδ0 H Λ N).range :=
    ArithmeticCompactness.HermitianArithmetic.principal_archimedean_discrete δ hδ hδ0 H hH hdet Λ hΛ N hN
  have hd := NumberTheory.ArithmeticGroups.Lattices.Discrete.Construction.discrete_map_of_closedMap (complexProjection δ hδ hδ0 H μ)
    (complexProjection_closed δ hδ hδ0 H μ hH hdef)
    (ArithmeticCompactness.HermitianArithmetic.principalArchimedeanHom δ hδ hδ0 H Λ N).range
  rw [MonoidHom.map_range, complexProjection_principal] at hd
  exact hd

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ArchimedeanCompactness.HermitianArithmetic
