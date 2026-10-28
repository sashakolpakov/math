import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleAffineFactorization
import OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceBoundIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceBoundOverlap

/-! # Pointed Coefficient Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A uniform coefficient bound on pointed étale neighborhoods controls every native atlas chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.hasBound_of_pointed_etale_charts (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (m : ℕ)
    (hlocal : ∀ x : X,
      ∃ (R : CommRingCat) (_ : Algebra ℂ R) (_ : Algebra ℚ R) (_ : Algebra.Smooth ℂ R)
        (j : Spec R ⟶ X), Etale j ∧ j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R ∧
        ∃ p : PrimeSpectrum R, j p = x ∧
        ∃ (L : Ideal R), J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel L ∧
        ∃ C : Component.CenterChoice.Construction.ComponentCenterChoice ℂ R L n, C.HasBound m) :
    ∀ i, (A.choice i).HasBound m := by
  intro i
  apply ((A.choice i).boundIdeal_eq_top_iff m).mp
  by_contra hnot
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal ((A.choice i).boundIdeal m) hnot
  let : P.IsMaximal := hP
  let p : PrimeSpectrum (A.rings i) := ⟨P, inferInstance⟩
  obtain ⟨R, akR, aqR, hsR, j, hj, hground, q, hq, L, hL, C, hb⟩ := hlocal (A.map i p)
  let : Algebra ℂ R := akR
  let : Algebra ℚ R := aqR
  let : Algebra.Smooth ℂ R := hsR
  let : Etale j := hj
  obtain ⟨S, akS, φ, ψ, hφ, hψ, hcomm, Q, hQp, _⟩ := Pointed.EtaleAffineFactorization.Construction.exists_pointed_global_etale_comparison
    f (A.rings i) R (A.map i) j (A.ground i) hground p q hq.symm
  let : Algebra ℂ S := akS
  have hJL : L.map ψ.toRingHom = (A.ideals i).map φ.toRingHom := by
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
    rw [← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, ← Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom,
      ← hL, ← A.ideal_eq i, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, hcomm]
  have hc := Component.CenterChoice.Construction.ComponentCenterChoice.hasBound_on_common_refinement ψ φ hψ hφ hJL C (A.choice i) hb
  have ht : ((A.choice i).boundIdeal m).map φ.toRingHom = ⊤ := by
    rw [(A.choice i).boundIdeal_map_etale φ hφ m]
    exact (((A.choice i).mapEtale φ hφ).boundIdeal_eq_top_iff m).mpr hc
  have hm : ((A.choice i).boundIdeal m).map φ.toRingHom ≤ Q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    exact hle.trans_eq (congrArg PrimeSpectrum.asIdeal hQp).symm
  rw [ht] at hm
  exact Q.isPrime.ne_top (top_le_iff.mp hm)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
