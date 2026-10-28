import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ReducedReesComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleAffineFactorization
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.EtaleBlowupCover

/-! # Reduced Rees Point Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.ReducedReesPointCover.Construction

noncomputable section

/-! Every chosen generating family gives actual pointed global Rees comparisons over an étale affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_globalReducedReesComparison_of_factorization
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (R : CommRingCat) [_root_.IsReduced R]
    (q : Spec R ⟶ X) (A : Ideal R) (hA : I.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel A)
    (U : X.affineOpens) (φ : Γ(X, U) →+* R) (hφ : φ.Etale)
    (hq : q = Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec)
    {κ : Type} (g : κ → A) (hgen : Ideal.span (Set.range (fun i => (g i).val)) = A)
    (x : GlobalBlowup.Data.Construction.globalBlowup I hI) (p : PrimeSpectrum R) (hp : q p = GlobalBlowup.Data.Construction.globalBlowupToBase I hI x) :
    ∃ i, ∃ P : PrimeSpectrum (Blowup.Charts.Construction.blowupChart A (g i)), ReducedReesComparison.Construction.globalReducedReesComparison I hI R q A hA (g i) P = x := by
  subst q
  have he : A = (I.ideal U).map φ := by
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
    exact hA.symm.trans (Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel I U φ)
  subst A
  obtain ⟨i, P, hP⟩ := EtaleBlowupCover.Construction.exists_generated_globalBlowup_baseChangeReesChart I hI U φ
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hφ).1 g hgen x p hp.symm
  refine ⟨i, P, ?_⟩
  rw [ReducedReesComparison.Construction.globalReducedReesComparison_eq_baseChange]
  exact hP

theorem exists_generated_globalReducedReesComparison_point
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (R : CommRingCat) [_root_.IsReduced R]
    (q : Spec R ⟶ X) [Etale q] (A : Ideal R) (hA : I.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel A)
    {κ : Type} (g : κ → A) (hgen : Ideal.span (Set.range (fun i => (g i).val)) = A)
    (x : GlobalBlowup.Data.Construction.globalBlowup I hI) (p : PrimeSpectrum R) (hp : q p = GlobalBlowup.Data.Construction.globalBlowupToBase I hI x) :
    ∃ i, ∃ P : PrimeSpectrum (Blowup.Charts.Construction.blowupChart A (g i)), ReducedReesComparison.Construction.globalReducedReesComparison I hI R q A hA (g i) P = x := by
  obtain ⟨U, S, φ, ψ, hopen, hψ, hcomm, Q, hQ⟩ := Pointed.EtaleAffineFactorization.Construction.exists_pointed_etale_affine_factorization R q p
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := hopen
  let : AlgebraicGeometry.IsReduced (Spec S) := isReduced_of_isOpenImmersion (Spec.map (CommRingCat.ofHom φ))
  let : _root_.IsReduced S := (affine_isReduced_iff S).mp inferInstance
  have hS : I.comap (Spec.map (CommRingCat.ofHom φ) ≫ q) = Affine.QuotientKernel.Construction.affineQuotientKernel (A.map φ) := by
    rw [Scheme.IdealSheafData.comap_comp, hA, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  let gS : κ → A.map φ := fun i => ⟨φ (g i).val, Ideal.mem_map_of_mem φ (g i).property⟩
  have hgenS : Ideal.span (Set.range (fun i => (gS i).val)) = A.map φ := by
    have h := congrArg (Ideal.map φ) hgen
    rw [Ideal.map_span, ← Set.range_comp] at h
    exact h
  have hQx : (Spec.map (CommRingCat.ofHom φ) ≫ q) Q = GlobalBlowup.Data.Construction.globalBlowupToBase I hI x := by
    change q (PrimeSpectrum.comap φ Q) = _
    rw [hQ]
    exact hp
  obtain ⟨i, P, hP⟩ := exists_globalReducedReesComparison_of_factorization I hI S _ (A.map φ) hS
    U ψ hψ hcomm gS hgenS x Q hQx
  refine ⟨i, PrimeSpectrum.comap (ChartLift.Construction.blowupChartMap A φ (g i)) P, ?_⟩
  have he := ReducedReesComparison.Construction.globalReducedReesComparison_refinement I hI R S q A hA (g i) φ hS
  have h := congrArg (fun u => u P) he
  exact h.trans hP

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.ReducedReesPointCover.Construction
