import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups
import OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

/-! # Matrix Realization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The literal principal special unitary group has a faithful matrix
realization in the original rational and distinguished complex SU groups. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (N : ℕ)

def Datum.RankThreePELDatum.principalRationalMatrix (g : Groups.principalSpecialUnitary P.b P.lattice N) : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b := by
  refine ⟨⟨LinearMap.toMatrix' g.val.toLinearMap, ?_⟩, ?_⟩
  · rw [LinearMap.det_toMatrix']
    have h := congrArg Units.val g.property.2.2
    simpa only [LinearEquiv.coe_det, Units.val_one] using h
  · intro x y
    change NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b
      (Matrix.toLin' (LinearMap.toMatrix' g.val.toLinearMap) x)
      (Matrix.toLin' (LinearMap.toMatrix' g.val.toLinearMap) y) = NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b x y
    rw [Matrix.toLin'_toMatrix']
    exact g.property.2.1 x y

theorem Datum.RankThreePELDatum.principalRationalMatrix_linear (g : Groups.principalSpecialUnitary P.b P.lattice N) :
    Matrix.SpecialLinearGroup.toLin' (P.principalRationalMatrix N g).val = g.val := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (Matrix.toLin'_toMatrix' g.val.toLinearMap) x

def Datum.RankThreePELDatum.principalRationalMatrixHom : Groups.principalSpecialUnitary P.b P.lattice N →* Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b where
  toFun := P.principalRationalMatrix N
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change LinearMap.toMatrix' (LinearMap.id : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) i j = (1 : Matrix (Fin 3) (Fin 3) E) i j
    rw [LinearMap.toMatrix'_id]
  map_mul' g h := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change LinearMap.toMatrix' (g.val.toLinearMap.comp h.val.toLinearMap) i j =
      (LinearMap.toMatrix' g.val.toLinearMap * LinearMap.toMatrix' h.val.toLinearMap) i j
    rw [LinearMap.toMatrix'_comp]

theorem Datum.RankThreePELDatum.principalRationalMatrixHom_injective : Function.Injective (P.principalRationalMatrixHom N) := by
  intro g h he
  apply Subtype.ext
  exact (P.principalRationalMatrix_linear N g).symm.trans
    ((congrArg (fun a : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b => Matrix.SpecialLinearGroup.toLin' a.val) he).trans
      (P.principalRationalMatrix_linear N h))

def Datum.RankThreePELDatum.principalArchimedeanMap : Groups.principalSpecialUnitary P.b P.lattice N →* Geometry.ComplexBall.ArithmeticQuotientEquationsData.ArchimedeanSU P.b P.μ :=
  (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap P.b P.μ).comp (P.principalRationalMatrixHom N)

theorem Datum.RankThreePELDatum.principalArchimedeanMap_injective : Function.Injective (P.principalArchimedeanMap N) :=
  (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap_injective P.b P.μ).comp (P.principalRationalMatrixHom_injective N)

def Datum.RankThreePELDatum.principalArchimedeanSubgroup : Subgroup (Geometry.ComplexBall.ArithmeticQuotientEquationsData.ArchimedeanSU P.b P.μ) := (P.principalArchimedeanMap N).range

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
