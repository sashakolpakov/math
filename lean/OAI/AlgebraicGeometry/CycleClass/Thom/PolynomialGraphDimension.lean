import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductDimension

/-! # Polynomial Graph Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialGraphDimension.Constructions

noncomputable section

/-! The native polynomial graph ambient has the actual base dimension plus its polynomial-coordinate dimension. The proof uses the genuine coordinate-ring transcendence degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DimensionBridge.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductDimension.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.TranscendenceDimension.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine Y.left] [IsIntegral Y.left] [Smooth Y.hom] (d : ℕ)

theorem graphTarget_dimension : Betti.AffineDimension.Realization.functionFieldDifferentialDimension (SchemeDivisor.GraphImage.Constructions.graphTarget Y d).hom =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom + d := by
  let : Algebra.FiniteType ℂ Γ(Y.left, ⊤) := ComplexPoints.Analytic.FiniteTypeSchemeTopology.affineOverGamma_finiteType Y
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension,
    ← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension]
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Γ(Y.left, ⊤) ⊗[ℂ] MvPolynomial (Fin d) ℂ)))) = _
  rw [Affine.DimensionBridge.Constructions.schemeTranscendenceDimension_spec_algebra, Tensor.TranscendenceDimension.Constructions.tensorProduct_trdeg,
    Cardinal.toNat_add (trdeg_lt_aleph0_of_finiteType (R := ℂ) (S := Γ(Y.left, ⊤)))
      (trdeg_lt_aleph0_of_finiteType (R := ℂ) (S := MvPolynomial (Fin d) ℂ)), Affine.ProductDimension.Constructions.affineOver_dimension]
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_id, Cardinal.toNat_natCast]

variable {N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral N.left] [Smooth N.hom] (j : Y ⟶ N) [IsOpenImmersion j.left]

include j in
omit [IsAffine Y.left] in
theorem openMap_nativeDimension : Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom := by
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension,
    ← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension]
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion j.left N.hom
  rw [j.w] at h
  exact h

include j in
theorem graphTarget_ambient_dimension : Betti.AffineDimension.Realization.functionFieldDifferentialDimension (SchemeDivisor.GraphImage.Constructions.graphTarget Y d).hom =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom + d :=
  (graphTarget_dimension Y d).trans (congrArg (fun n => n + d) (openMap_nativeDimension Y j))

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (z : {x : X.left // Order.coheight x = 1})

include j in
theorem primeGraph_codimension (q : ℕ)
    (hq : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + q =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension (SchemeDivisor.GraphImage.Constructions.graphTarget Y d).hom) :
    Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension
      (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Scheme.RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)).hom) → ℂ)
      ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) = q + 1 := by
  change Module.finrank ℂ ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) -
    Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Scheme.RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)).hom) → ℂ) = _
  simp only [Module.finrank_prod, Module.finrank_fin_fun]
  have hd := graphTarget_ambient_dimension Y d j
  have hz := SchemeDivisor.Purity.Constructions.primeRegularDimension_add_one X z
  omega

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialGraphDimension.Constructions
