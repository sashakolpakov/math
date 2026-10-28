import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiEndAdditivity
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonRelations
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality

/-! # Extending Additivity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingAdditivity.CM

noncomputable section

/-! Additivity on crystalline H1 for genuinely extending endomorphisms
is a consequence of Betti H1 and the complete comparison proposition.
The complex fiber retains its given scheme, group, and projective embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)

def addEnd (f g : A.ExtendingEndomorphism) : A.ExtendingEndomorphism where
  generic := f.generic + g.generic
  integral := f.integral + g.integral
  compatible := by
    let bi := NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q])
    let bg := NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq
    let fi : (A.integral.pullback bi).scheme ⟶ (A.integral.pullback bi).scheme :=
      (Over.pullback bi).map f.integral.toMul.hom.hom
    let gi : (A.integral.pullback bi).scheme ⟶ (A.integral.pullback bi).scheme :=
      (Over.pullback bi).map g.integral.toMul.hom.hom
    let fg : (A.variety.pullback bg).scheme ⟶ (A.variety.pullback bg).scheme :=
      (Over.pullback bg).map f.generic.toMul.hom.hom
    let gg : (A.variety.pullback bg).scheme ⟶ (A.variety.pullback bg).scheme :=
      (Over.pullback bg).map g.generic.toMul.hom.hom
    let : IsMonHom A.genericIso.hom := A.genericIso_group
    change (Over.pullback bi).map (f.integral.toMul.hom.hom * g.integral.toMul.hom.hom) ≫
      A.genericIso.hom = A.genericIso.hom ≫
        (Over.pullback bg).map (f.generic.toMul.hom.hom * g.generic.toMul.hom.hom)
    calc
      _ = (fi * gi) ≫ A.genericIso.hom := congrArg (· ≫ A.genericIso.hom)
        ((Over.pullback bi).map_mul f.integral.toMul.hom.hom g.integral.toMul.hom.hom)
      _ = (fi ≫ A.genericIso.hom) * (gi ≫ A.genericIso.hom) := MonObj.mul_comp fi gi _
      _ = (A.genericIso.hom ≫ fg) * (A.genericIso.hom ≫ gg) :=
        congrArg₂ (· * ·) f.compatible g.compatible
      _ = A.genericIso.hom ≫ (fg * gg) := (MonObj.comp_mul _ fg gg).symm
      _ = _ := congrArg (A.genericIso.hom ≫ ·)
        ((Over.pullback bg).map_mul f.generic.toMul.hom.hom g.generic.toMul.hom.hom).symm

theorem special_addEnd (f g : A.ExtendingEndomorphism) :
    A.specialEndomorphism (addEnd A f g) = A.specialEndomorphism f * A.specialEndomorphism g :=
  (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))).map_mul
    f.integral.toMul.hom.hom g.integral.toMul.hom.hom

theorem complex_addEnd (j : K →+* ℂ) (f g : A.ExtendingEndomorphism) :
    A.complexEndomorphism j (addEnd A f g) =
      A.complexEndomorphism j f * A.complexEndomorphism j g :=
  (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap j)).map_mul f.generic.toMul.hom.hom g.generic.toMul.hom.hom

def complexAbelianVariety (j : K →+* ℂ)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom) :
    ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := by
  let : SmoothOfRelativeDimension A.dimension (A.complexFiber j).scheme.hom :=
    (A.complexFiber j).smoothDimension
  let : Smooth (A.complexFiber j).scheme.hom :=
    SmoothOfRelativeDimension.smooth A.dimension (A.complexFiber j).scheme.hom
  have : ConnectedSpace (A.complexFiber j).scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (A.complexFiber j).scheme.hom
  have hIntegral : IsIntegral (A.complexFiber j).scheme.left :=
    ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_connected_scheme_integral (A.complexFiber j).scheme.hom
  exact {
    variety := ⟨A.smoothProjectiveFiber j P, hIntegral⟩
    group := (A.complexFiber j).group
    commutative := (A.complexFiber j).commutative }

theorem complexBetti_addEnd (j : K →+* ℂ)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (f g : A.ExtendingEndomorphism) :
    A.complexBettiPullback j (addEnd A f g) =
      A.complexBettiPullback j f + A.complexBettiPullback j g := by
  change (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (A.complexEndomorphism j (addEnd A f g))).hom = _
  rw [complex_addEnd]
  exact BettiEndAdditivity.CM.complex_pullback_mul_map (complexAbelianVariety A j P)
    (A.complexEndomorphism j f) (A.complexEndomorphism j g)

theorem crystalline_addEnd_of_full_comparison
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (iota : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hcomparison : NumberTheory.PadicHodge.GeometricComparison.HeckeScalar.ComparisonTarget q κ jComplex iota jq A H ρ P ℓ)
    (f g : A.ExtendingEndomorphism) :
    A.crystallinePullback (addEnd A f g) = A.crystallinePullback f + A.crystallinePullback g := by
  let fs : Fin 3 → A.ExtendingEndomorphism := ![addEnd A f g, f, g]
  let cs : Fin 3 → ℤ := ![1, -1, -1]
  have hb : (∑ i : Fin 3, cs i • A.complexBettiPullback (jComplex.comp κ) (fs i)) = 0 := by
    simp only [Fin.sum_univ_three, fs, cs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_smul, neg_smul, complexBetti_addEnd A _ P]
    abel
  have hc := ComparisonRelations.CM.crystalline_relations_of_full_comparison A κ jComplex iota
    ρ P ℓ hcomparison Finset.univ fs cs hb
  simp only [Fin.sum_univ_three, fs, cs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_smul, neg_smul] at hc
  apply sub_eq_zero.mp
  calc
    _ = A.crystallinePullback (addEnd A f g) + -A.crystallinePullback f +
        -A.crystallinePullback g := by abel
    _ = 0 := hc

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingAdditivity.CM
