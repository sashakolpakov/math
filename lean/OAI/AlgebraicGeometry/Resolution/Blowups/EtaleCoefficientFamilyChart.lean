import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.FamilyCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.GlobalCoefficientEtalePullback

/-! # Etale Coefficient Family Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Initial fixed-family data on any actual étale chart with a normalized normal derivation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart.ofEtaleNormal
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData) (b : ℕ)
    (R : CommRingCat) [Algebra ℂ R] (j : Spec R ⟶ X) [Etale j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (z : R)
    (hH : H.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z}))
    (K : Ideal R) (hK : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K)
    (D : Derivation ℂ R R) (hD : D z = 1) :
    GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι) b := by
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {z})))
  have hker : H.subschemeι.ker ≤ (i ≫ j).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    apply (ControlledIdealKernel.Construction.idealSheaf_le_ker_iff_comap_eq_bot H (i ≫ j)).mpr
    rw [Scheme.IdealSheafData.comap_comp, hH]
    exact (ControlledIdealKernel.Construction.idealSheaf_le_ker_iff_comap_eq_bot _ i).mp le_rfl
  let l := IsClosedImmersion.lift H.subschemeι (i ≫ j) hker
  have hl : l ≫ H.subschemeι = i ≫ j := IsClosedImmersion.lift_fac _ _ _
  let p : K → R := Subtype.val
  have hp : Ideal.span (Set.range p) = K := by
    change Ideal.span (Set.range (Subtype.val : K → R)) = K
    rw [Subtype.range_val, Ideal.span_eq]
  refine {
    ring := R
    algebra := inferInstance
    map := j
    etale := inferInstance
    ground := hj
    normal := z
    hypersurface := hH
    derivative := D
    derivative_normal := hD
    familyIndex := K
    family := p
    familyIdeal := by rw [hp]; exact hK
    coefficientMap := l
    coefficient_over := hl
    coefficientIdeal := Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal ℂ z K b
    coefficient_eq := ?_
    lower := ?_ }
  · exact Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothCoefficientIdealSheaf_comap_etale_hypersurface_chart f J b H.subschemeι R j hj
      K z hK l hl
  · have h := Relative.CoefficientFamilyInterval.Construction.weightedCoordinateDerivativeFamilyIdeal_le_relative ℂ D z p b
    rwa [hp] at h

end

end OAI.AlgebraicGeometry.Resolution.Blowups
