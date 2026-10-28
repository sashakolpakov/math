import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Transform
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.FamilyCharts

/-! # Chart Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ChartTransform.Construction

noncomputable section

/-! Exact retained native coefficients on an actual divided-hypersurface blowup chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalRetainedCoefficientTransform_comap_hypersurface_chart
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J H : X.IdealSheafData} {C : H.subscheme.IdealSheafData} {b : ℕ}
    (T : FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b) [IsNoetherianRing T.ring] [Algebra ℚ T.ring]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hp : C ≤ (I.comap H.subschemeι) ^ b.factorial)
    (A : Ideal T.ring) (hA : I.comap T.map = Affine.QuotientKernel.Construction.affineQuotientKernel A)
    (hn : T.normal ∈ A) (a : A) (ha : T.derivative a.val = 0)
    (j : Spec (.of (Blowup.Charts.Construction.blowupChart A a)) ⟶ GlobalBlowup.Data.Construction.globalBlowup I hI)
    (hover : j ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI =
      Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants A a)) ≫ T.map)
    (l : Spec (.of (Blowup.Charts.Construction.blowupChart A a ⧸ Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio A a ⟨T.normal, hn⟩})) ⟶
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme)
    (hl : l ≫ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio A a ⟨T.normal, hn⟩}))) ≫ j) :
    (Transform.Construction.globalRetainedCoefficientTransform I H C hI b).comap l =
      Affine.QuotientKernel.Construction.affineQuotientKernel ((T.coefficientIdeal.map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap A a ⟨T.normal, hn⟩)).colon
        (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio A a ⟨T.normal, hn⟩})
          (Blowup.Charts.Construction.blowupChartConstants A a a.val)) ^ b.factorial})) := by
  let z : A := ⟨T.normal, hn⟩
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio A a z})))
  let t := Spec.map (CommRingCat.ofHom (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap A a z))
  let v := Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants A a))
  have ht : t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {T.normal}))) = q ≫ v := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hcomm : l ≫ Transform.Construction.globalControlledCarrierMap I H hI = t ≫ T.coefficientMap := by
    apply (cancel_mono H.subschemeι).mp
    calc
      _ = (l ≫ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι) ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI := by
        rw [Category.assoc, Transform.Construction.globalControlledCarrierMap_over, ← Category.assoc]
      _ = q ≫ (j ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) := by rw [hl, Category.assoc]
      _ = (q ≫ v) ≫ T.map := by rw [hover]; exact (Category.assoc _ _ _).symm
      _ = (t ≫ T.coefficientMap) ≫ H.subschemeι := by
        rw [Category.assoc t T.coefficientMap H.subschemeι, T.coefficient_over,
          ← Category.assoc t _ T.map, ht]
  apply Transform.Construction.globalRetainedCoefficientTransform_comap_regular_chart I H C hI b hp
    (.of (Blowup.Charts.Construction.blowupChart A a ⧸ Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio A a z})) l
    (T.coefficientIdeal.map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap A a z))
    (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio A a z}) (Blowup.Charts.Construction.blowupChartConstants A a a.val))
    (NoetherianCoordinateTransform.Construction.blowupHypersurface_exceptionalParameter_regular A a z (T.derivative.restrictScalars ℤ)
      ha T.derivative_normal)
  · rw [← Scheme.IdealSheafData.comap_comp, hcomm, Scheme.IdealSheafData.comap_comp,
      T.coefficient_eq, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  · rw [← Scheme.IdealSheafData.comap_comp, hcomm, Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp I T.coefficientMap H.subschemeι,
      T.coefficient_over, Scheme.IdealSheafData.comap_comp,
      hA, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Ideal.map_map]
    have he : (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap A a z).comp (Ideal.Quotient.mk (Ideal.span {T.normal})) =
        (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio A a z})).comp (Blowup.Charts.Construction.blowupChartConstants A a) := rfl
    rw [he, ← Ideal.map_map, ExceptionalIdeal.Construction.blowupChart_extendedIdeal, Ideal.map_span, Set.image_singleton]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ChartTransform.Construction
