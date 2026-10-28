import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ArithmeticModel
import OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel
import OAI.RepresentationTheory.Theta.Adelic.UnitaryCoordinateTopology
import OAI.Geometry.ComplexBall.ArithmeticPresentation

/-! # Archimedean Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ArchimedeanModel.HermitianArithmetic

noncomputable section

/-! The distinguished real factor of an arbitrary ReferenceFamily Hermitian group
is the original complex matrix group. Its rational action is entrywise
application of the specified embedding, with no change of lattice. -/

open scoped Classical
open _root_.NumberField

private def matrixCongr {R : Type} [CommRing R] [StarRing R] [TopologicalSpace R]
    (H K : Matrix (Fin 3) (Fin 3) R) (h : H = K) :
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H ≃ₜ* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU K where
  toFun g := ⟨g.val, h ▸ g.property⟩
  invFun g := ⟨g.val, h.symm ▸ g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

private theorem realQuadraticEquiv_continuous (d r : ℝ)
    (hr : r ^ 2 = -d) (hr0 : r ≠ 0) : Continuous (Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticEquiv d r hr hr0) := by
  change Continuous (fun z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d => Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticHom d r hr z)
  simp_rw [Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticHom_apply]
  exact (Complex.continuous_ofReal.comp (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re d)).add
    ((Complex.continuous_ofReal.comp (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im d)).mul continuous_const)

private theorem realQuadraticEquiv_inverse_continuous (d r : ℝ)
    (hr : r ^ 2 = -d) (hr0 : r ≠ 0) : Continuous (Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticEquiv d r hr hr0).symm := by
  have he (z : ℂ) : (Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticEquiv d r hr hr0).symm z =
      Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticInverse d r z := by
    apply (Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticEquiv d r hr hr0).injective
    rw [RingEquiv.apply_symm_apply]
    exact (Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadratic_right_inverse d r hr hr0 z).symm
  change Continuous (fun z : ℂ => (Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticEquiv d r hr hr0).symm z)
  simp_rw [he]
  apply (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff d _).mpr
  exact ⟨Complex.continuous_re, Complex.continuous_im.div_const r⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (H : Matrix (Fin 3) (Fin 3) E) (μ : E →+* ℂ)

def realForm : Matrix (Fin 3) (Fin 3)
    (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ))) :=
  (ArithmeticModel.HermitianArithmetic.quadraticMatrix δ hδ hδ0 H).map
    (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ) (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ))

theorem realForm_complex :
    (realForm δ hδ hδ0 H μ).map
      (Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticEquiv (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ)) (μ δ).im
        (Geometry.ComplexBall.Archimedean.ArithmeticQuotient.imaginary_embedding_im_sq δ hδ μ)
        (Geometry.ComplexBall.Archimedean.ArithmeticQuotient.imaginary_embedding_im_ne_zero δ hδ hδ0 μ)).toRingHom = H.transpose.map μ := by
  apply Matrix.ext
  intro i j
  change Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticHom _ _ (Geometry.ComplexBall.Archimedean.ArithmeticQuotient.imaginary_embedding_im_sq δ hδ μ) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap _ _
    ((Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm (H j i))) = μ (H j i)
  rw [Geometry.ComplexBall.Archimedean.ArithmeticQuotient.realQuadraticHom_scalarExtension δ hδ hδ0 μ, AlgEquiv.apply_symm_apply]

def realPointsEquiv :
    (ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H).Points (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ) ≃ₜ*
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.transpose.map μ) :=
  (RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel.Topology.regularUnitaryContinuousEquiv
    (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ)) (realForm δ hδ hδ0 H μ)).symm.trans
    ((RepresentationTheory.Theta.Adelic.UnitaryCoordinateTopology.specialUnitaryFieldContinuousEquiv
      (Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticEquiv (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ)) (μ δ).im
        (Geometry.ComplexBall.Archimedean.ArithmeticQuotient.imaginary_embedding_im_sq δ hδ μ) (Geometry.ComplexBall.Archimedean.ArithmeticQuotient.imaginary_embedding_im_ne_zero δ hδ hδ0 μ))
      (Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticEquiv_star _ _ _ _)
      (realQuadraticEquiv_continuous _ _ _ _) (realQuadraticEquiv_inverse_continuous _ _ _ _)
      (realForm δ hδ hδ0 H μ)).trans
        (matrixCongr _ _ (realForm_complex δ hδ hδ0 H μ)))

theorem realPointsEquiv_entry
    (g : (ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H).Points (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ)) (i j : Fin 3) :
    (realPointsEquiv δ hδ hδ0 H μ g).val.val i j =
      Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticHom (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ)) (μ δ).im
        (Geometry.ComplexBall.Archimedean.ArithmeticQuotient.imaginary_embedding_im_sq δ hδ μ)
        (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ)) g.val.val i j) := by
  change Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticHom _ _ (Geometry.ComplexBall.Archimedean.ArithmeticQuotient.imaginary_embedding_im_sq δ hδ μ)
    (((RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel.regularUnitaryEquiv
      (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ))
      (realForm δ hδ hδ0 H μ)).symm g).val.val i j) = _
  exact congrArg (fun M : Matrix (Fin 3) (Fin 3)
      (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ))) =>
      Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticHom _ _ (Geometry.ComplexBall.Archimedean.ArithmeticQuotient.imaginary_embedding_im_sq δ hδ μ) (M i j))
    (RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel.Topology.regularUnitaryEquiv_inverse_matrix
      (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ (Geometry.ComplexBall.ArithmeticQuotientEquationsData.imaginarySquare δ hδ)) (realForm δ hδ hδ0 H μ) g)

theorem realPointsEquiv_diagonal_matrix
    (g : Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H)) :
    (realPointsEquiv δ hδ hδ0 H μ
      ((ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H).map (RingHom.id _) (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ)
        (ArithmeticModel.HermitianArithmetic.rationalEquiv δ hδ hδ0 H g))).val.val =
      (LinearMap.toMatrix' g.val.toLinearMap).map μ := by
  apply Matrix.ext
  intro i j
  rw [realPointsEquiv_entry]
  change Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticHom _ _ (Geometry.ComplexBall.Archimedean.ArithmeticQuotient.imaginary_embedding_im_sq δ hδ μ) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix _
    ((ArithmeticModel.HermitianArithmetic.rationalEquiv δ hδ hδ0 H g).val.val.map (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ)) i j) =
      μ (LinearMap.toMatrix' g.val.toLinearMap i j)
  rw [ArithmeticModel.HermitianArithmetic.rationalEquiv_matrix, ← Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix_map, Geometry.ComplexBall.ArithmeticQuotientEquationsData.decode_regularMatrix]
  change Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient.realQuadraticHom _ _ (Geometry.ComplexBall.Archimedean.ArithmeticQuotient.imaginary_embedding_im_sq δ hδ μ) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap _ _
    ((Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm (LinearMap.toMatrix' g.val.toLinearMap i j))) = _
  rw [Geometry.ComplexBall.Archimedean.ArithmeticQuotient.realQuadraticHom_scalarExtension δ hδ hδ0 μ, AlgEquiv.apply_symm_apply]

def atPlaceEquiv : (ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H).AtPlace (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace μ) ≃ₜ*
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.transpose.map μ) :=
  (Geometry.ComplexBall.ArithmeticPresentation.Quotient.completedRealPointsEquiv (ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H) (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace μ)
    (IsTotallyReal.isReal _)).trans
      ((Geometry.ComplexBall.ArithmeticPresentation.Quotient.matrixPointsCongr _ _ _ (Geometry.ComplexBall.ArithmeticPresentation.Quotient.realPlaceEmbedding_eq_realEmbedding μ)).trans
        (realPointsEquiv δ hδ hδ0 H μ))

theorem atPlaceEquiv_diagonal_matrix
    (g : Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H)) :
    (atPlaceEquiv δ hδ hδ0 H μ
      ((ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H).diagonalAtPlace (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace μ)
        (ArithmeticModel.HermitianArithmetic.rationalEquiv δ hδ hδ0 H g))).val.val =
      (LinearMap.toMatrix' g.val.toLinearMap).map μ := by
  let G := ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H
  let w := Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace μ
  let hv := IsTotallyReal.isReal w
  have he : Geometry.ComplexBall.ArithmeticPresentation.Quotient.matrixPointsCongr G _ _ (Geometry.ComplexBall.ArithmeticPresentation.Quotient.realPlaceEmbedding_eq_realEmbedding μ)
      (Geometry.ComplexBall.ArithmeticPresentation.Quotient.completedRealPointsEquiv G w hv (G.diagonalAtPlace w
        (ArithmeticModel.HermitianArithmetic.rationalEquiv δ hδ hδ0 H g))) =
      G.map (RingHom.id _) (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding μ) (ArithmeticModel.HermitianArithmetic.rationalEquiv δ hδ hδ0 H g) := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change InfinitePlace.Completion.ringEquivRealOfIsReal hv
      (algebraMap (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) w.Completion
        ((ArithmeticModel.HermitianArithmetic.rationalEquiv δ hδ hδ0 H g).val i j)) = _
    have hx := RingHom.congr_fun (NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup.realPlaceEmbedding_eq w hv)
      ((ArithmeticModel.HermitianArithmetic.rationalEquiv δ hδ hδ0 H g).val i j)
    change _ = w.embedding_of_isReal hv _ at hx
    rw [Geometry.ComplexBall.ArithmeticPresentation.Quotient.realPlaceEmbedding_eq_realEmbedding μ] at hx
    exact hx
  exact (congrArg (fun a => (realPointsEquiv δ hδ hδ0 H μ a).val.val) he).trans
    (realPointsEquiv_diagonal_matrix δ hδ hδ0 H μ g)

def complexHom : Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H) →*
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.transpose.map μ) :=
  (atPlaceEquiv δ hδ hδ0 H μ).toMonoidHom.comp
    (((ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H).diagonalAtPlace (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realPlace μ)).comp
      (ArithmeticModel.HermitianArithmetic.rationalEquiv δ hδ hδ0 H).toMonoidHom)

theorem complexHom_matrix
    (g : Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H)) :
    (complexHom δ hδ hδ0 H μ g).val.val = (LinearMap.toMatrix' g.val.toLinearMap).map μ :=
  atPlaceEquiv_diagonal_matrix δ hδ hδ0 H μ g

theorem complexHom_injective : Function.Injective (complexHom δ hδ hδ0 H μ) := by
  intro g k hgk
  have hm := congrArg (fun a : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.transpose.map μ) => a.val.val) hgk
  rw [complexHom_matrix, complexHom_matrix] at hm
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.toMatrix'.injective
  apply Matrix.ext
  intro i j
  exact μ.injective (congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A i j) hm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ArchimedeanModel.HermitianArithmetic
