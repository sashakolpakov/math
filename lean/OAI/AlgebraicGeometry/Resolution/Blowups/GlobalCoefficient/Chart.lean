import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.GlobalCoefficientChart

/-! # Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The actual native hypersurface and coefficient-base maps of retained charts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart.coefficient_isPullback
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J H : X.IdealSheafData}
    {C : H.subscheme.IdealSheafData} {b : ℕ} (T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {T.normal}))))
      T.coefficientMap T.map H.subschemeι := by
  apply isPullback_of_isClosedImmersion _ _ _ _ T.coefficient_over.symm
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact T.hypersurface

theorem GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart.coefficient_etale
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J H : X.IdealSheafData}
    {C : H.subscheme.IdealSheafData} {b : ℕ} (T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b) :
    Etale T.coefficientMap :=
  MorphismProperty.of_isPullback T.coefficient_isPullback T.etale

attribute [instance] GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart.coefficient_etale

def Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction.baseMap
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J H : X.IdealSheafData}
    {C : H.subscheme.IdealSheafData} {b : ℕ} {T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b}
    (A : Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction T) : Spec A.base ⟶ H.subscheme :=
  Spec.map (CommRingCat.ofHom A.retraction.toRingHom) ≫ T.coefficientMap

theorem Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction.baseMap_etale
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J H : X.IdealSheafData}
    {C : H.subscheme.IdealSheafData} {b : ℕ} {T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b}
    (A : Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction T) : Etale A.baseMap := by
  let : Etale (Spec.map (CommRingCat.ofHom A.retraction.toRingHom)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.Etale.of_bijective A.retraction.bijective)
  unfold Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction.baseMap
  infer_instance

theorem Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction.baseMap_coefficient
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J H : X.IdealSheafData}
    {C : H.subscheme.IdealSheafData} {b : ℕ} {T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b}
    (A : Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction T) :
    C.comap A.baseMap = Affine.QuotientKernel.Construction.affineQuotientKernel (T.coefficientIdeal.map A.retraction.toRingHom) := by
  rw [Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction.baseMap, Scheme.IdealSheafData.comap_comp, T.coefficient_eq, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]

theorem Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction.baseMap_ground
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J H : X.IdealSheafData}
    {C : H.subscheme.IdealSheafData} {b : ℕ} {T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b}
    (A : Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction T) :
    A.baseMap ≫ (H.subschemeι ≫ f) = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure A.base := by
  have he : A.retraction.toRingHom.comp
      ((Ideal.Quotient.mk (Ideal.span {T.normal})).comp (algebraMap ℂ T.ring)) =
        algebraMap ℂ A.base := by
    apply RingHom.ext
    intro c
    change A.retraction (Ideal.Quotient.mk (Ideal.span {T.normal}) (algebraMap ℂ T.ring c)) = _
    rw [IsScalarTower.algebraMap_apply ℂ A.base T.ring]
    exact A.retraction.commutes (algebraMap ℂ A.base c)
  calc
    _ = Spec.map (CommRingCat.ofHom A.retraction.toRingHom) ≫
        T.coefficientMap ≫ H.subschemeι ≫ f := by simp only [Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction.baseMap, Category.assoc]
    _ = Spec.map (CommRingCat.ofHom A.retraction.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {T.normal}))) ≫ T.map ≫ f := by
      rw [← Category.assoc T.coefficientMap H.subschemeι f, T.coefficient_over, Category.assoc]
    _ = _ := by
      rw [T.ground, ComplexAffineDifferentialIdeal.Construction.complexSpecStructure, ← Spec.map_comp, ← Spec.map_comp]
      exact congrArg (fun φ : ℂ →+* A.base => Spec.map (CommRingCat.ofHom φ)) he

end

end OAI.AlgebraicGeometry.Resolution.Blowups
