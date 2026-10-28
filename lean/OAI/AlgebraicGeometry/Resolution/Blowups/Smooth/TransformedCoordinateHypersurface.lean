import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Hypersurface
import OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BlowupChart

/-! # Transformed Coordinate Hypersurface -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface.Construction

noncomputable section

/-! Smooth coordinate hypersurfaces in actual blowup charts and under étale extension. -/

open _root_.MvPolynomial

universe u

variable {R σ : Type u} [CommRing R] [Finite σ]

/-- A coordinate hyperplane is smooth over its coefficient ring. -/
theorem coordinateHyperplane_smooth (j : σ) :
    Algebra.Smooth R (MvPolynomial σ R ⧸ Ideal.span {(X j : MvPolynomial σ R)}) := by
  let P : Algebra.SubmersivePresentation R (HypersurfaceChart.Construction.hypersurfaceRing (X j : MvPolynomial σ R)) σ Unit :=
    { toPreSubmersivePresentation := HypersurfaceChart.Construction.hypersurfacePreSubmersive (X j) j
      jacobian_isUnit := by
        rw [HypersurfaceChart.Construction.hypersurfacePreSubmersive_jacobian, pderiv_X_self, map_one]
        exact isUnit_one }
  let : Algebra.IsStandardSmooth R (HypersurfaceChart.Construction.hypersurfaceRing (X j : MvPolynomial σ R)) := P.isStandardSmooth
  infer_instance

attribute [local instance] Coordinate.CenterBlowup.Construction.coordinateCenterBlowupAlgebra

/-- On every coordinate-center chart whose denominator is a different
coordinate, the divided coordinate hypersurface remains smooth. -/
theorem coordinateCenterBlowupHypersurface_smooth (i j : σ) (hji : j ≠ i) :
    Algebra.Smooth R (Coordinate.CenterBlowup.Construction.coordinateCenterBlowupChart (R := R) i ⧸
      Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio (idealOfVars σ R) (Coordinate.CenterBlowup.Construction.coordinateCenterElement i) (Coordinate.CenterBlowup.Construction.coordinateCenterElement j)}) := by
  let : Algebra.Smooth R (MvPolynomial σ R ⧸ Ideal.span {(X j : MvPolynomial σ R)}) :=
    coordinateHyperplane_smooth j
  have he : Ideal.span {(X j : MvPolynomial σ R)} =
      (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio (idealOfVars σ R) (Coordinate.CenterBlowup.Construction.coordinateCenterElement i) (Coordinate.CenterBlowup.Construction.coordinateCenterElement j)}).map
        (Coordinate.CenterBlowup.Construction.coordinateCenterBlowupChartAlgEquiv (R := R) i).toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x : MvPolynomial σ R => Ideal.span {x})
      (Coordinate.CenterBlowup.Construction.coordinateBlowupToPolynomial_ratio (R := R) i j hji).symm
  exact Algebra.Smooth.of_equiv
    (Ideal.quotientEquivAlg _ _ (Coordinate.CenterBlowup.Construction.coordinateCenterBlowupChartAlgEquiv (R := R) i) he).symm

section Etale

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B] [Algebra.Etale A B]

omit [Algebra.Etale A B] in
/-- The canonical quotient extension is compatible with the original coefficient base. -/
theorem extendedQuotient_scalarTower (I : Ideal A) :
    IsScalarTower k (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := by
  apply IsScalarTower.of_algebraMap_eq (R := k) (S := A ⧸ I) (A := B ⧸ I.map (algebraMap A B))
  intro r
  rw [IsScalarTower.algebraMap_apply k A (A ⧸ I),
    ← IsScalarTower.algebraMap_apply A (A ⧸ I)]
  exact IsScalarTower.algebraMap_apply k A _ r

/-- Smoothness of a closed subscheme persists under the actual extended
ideal of an étale ambient map. -/
theorem smooth_etale_extended_quotient (I : Ideal A) [Algebra.Smooth k (A ⧸ I)] :
    Algebra.Smooth k (B ⧸ I.map (algebraMap A B)) := by
  let : IsScalarTower k (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := extendedQuotient_scalarTower I
  let : Algebra.Etale (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := Coordinate.Hypersurface.Construction.etale_quotient_of_etale I
  exact Algebra.Smooth.comp k (A ⧸ I) (B ⧸ I.map (algebraMap A B))

end Etale

variable {A B k : Type u} [CommRing A] [CommRing B] [CommRing k]
  [Algebra A B] [Algebra.Etale A B]

attribute [local instance] Blowups.Etale.BlowupChart.Construction.etaleBlowupChartAlgebra

/-- A smooth divided hypersurface in a source blowup chart remains smooth
in the corresponding étale chart. Its defining equation is the actual mapped ratio. -/
theorem smooth_transformedHypersurface_of_etale (I : Ideal A) (a z : I)
    [Algebra k (Blowups.Blowup.Charts.Construction.blowupChart I a)] [Algebra k (ChartFlatBaseChange.Construction.blowupBaseChangedChart (S := B) I a)]
    [IsScalarTower k (Blowups.Blowup.Charts.Construction.blowupChart I a) (ChartFlatBaseChange.Construction.blowupBaseChangedChart (S := B) I a)]
    [Algebra.Smooth k (Blowups.Blowup.Charts.Construction.blowupChart I a ⧸ Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})] :
    Algebra.Smooth k (ChartFlatBaseChange.Construction.blowupBaseChangedChart (S := B) I a ⧸
      Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio (I.map (algebraMap A B))
        ⟨algebraMap A B a.val, Ideal.mem_map_of_mem _ a.property⟩
        ⟨algebraMap A B z.val, Ideal.mem_map_of_mem _ z.property⟩}) := by
  let : Algebra.Etale (Blowups.Blowup.Charts.Construction.blowupChart I a) (ChartFlatBaseChange.Construction.blowupBaseChangedChart (S := B) I a) :=
    Blowups.Etale.BlowupChart.Construction.blowupChartMap_algebra_etale I a
  let J : Ideal (Blowups.Blowup.Charts.Construction.blowupChart I a) := Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}
  let φ : Blowups.Blowup.Charts.Construction.blowupChart I a →+* ChartFlatBaseChange.Construction.blowupBaseChangedChart (S := B) I a :=
    @algebraMap (Blowups.Blowup.Charts.Construction.blowupChart I a) (ChartFlatBaseChange.Construction.blowupBaseChangedChart (S := B) I a)
      inferInstance inferInstance inferInstance
  let : Algebra.Smooth k (ChartFlatBaseChange.Construction.blowupBaseChangedChart (S := B) I a ⧸ J.map φ) :=
    smooth_etale_extended_quotient J
  have he : J.map φ = Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio (I.map (algebraMap A B))
      ⟨algebraMap A B a.val, Ideal.mem_map_of_mem _ a.property⟩
      ⟨algebraMap A B z.val, Ideal.mem_map_of_mem _ z.property⟩} := by
    change (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}).map (ChartLift.Construction.blowupChartMap I (algebraMap A B) a) = _
    rw [Ideal.map_span, Set.image_singleton, Blowups.Etale.BlowupChart.Construction.blowupChartMap_ratio]
  exact Algebra.Smooth.of_equiv (Ideal.quotientEquivAlgOfEq k he)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface.Construction
