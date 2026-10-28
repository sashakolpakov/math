import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleAffineFactorization
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.FlatContainment
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelOrderEquiv

/-! # Etale Ideal Sheaf Containment -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleIdealSheafContainment.Construction

noncomputable section

/-! Actual pointed étale affine charts detect containment of native ideal sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem idealSheaf_le_of_pointed_etale_charts
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I J : X.IdealSheafData)
    (hlocal : ∀ x : X, ∃ (R : CommRingCat) (_ : Algebra ℂ R) (j : Spec R ⟶ X),
      Etale j ∧ j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R ∧
      ∃ q : PrimeSpectrum R, j q = x ∧ I.comap j ≤ J.comap j) : I ≤ J := by
  intro U
  let : Algebra ℂ Γ(X, U) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  apply FlatContainment.Construction.ideal_le_of_pointed_flat_charts
  intro p
  obtain ⟨R, aR, j, hj, hg, q, hq, hIJ⟩ := hlocal (U.2.fromSpec p)
  let : Algebra ℂ R := aR
  let : Etale j := hj
  obtain ⟨S, aS, φ, ψ, hφ, hψ, hcomm, Q, hQ, _⟩ := EtaleAffineFactorization.Construction.exists_pointed_global_etale_comparison f
    Γ(X, U) R U.2.fromSpec j (Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U).symm hg p q hq.symm
  let : Algebra ℂ S := aS
  refine ⟨S, φ.toRingHom, (RingHom.Etale.iff_flat_and_formallyUnramified.mp hφ).1, Q, hQ, ?_⟩
  apply (Affine.IdealChartDescent.Construction.affineQuotientKernel_le_iff _ _).mp
  calc
    Affine.QuotientKernel.Construction.affineQuotientKernel ((I.ideal U).map φ.toRingHom) =
        I.comap (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ U.2.fromSpec) :=
      (Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel I U φ.toRingHom).symm
    _ = (I.comap j).comap (Spec.map (CommRingCat.ofHom ψ.toRingHom)) := by
      rw [hcomm, Scheme.IdealSheafData.comap_comp]
    _ ≤ (J.comap j).comap (Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
      Scheme.IdealSheafData.comap_mono _ hIJ
    _ = J.comap (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ U.2.fromSpec) := by
      rw [← Scheme.IdealSheafData.comap_comp, ← hcomm]
    _ = Affine.QuotientKernel.Construction.affineQuotientKernel ((J.ideal U).map φ.toRingHom) :=
      Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel J U φ.toRingHom

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleIdealSheafContainment.Construction
