import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ReducedReesComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleAffineFactorization
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOpenBaseChange

/-! # Reduced Rees Etale -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.ReducedReesEtale.Construction

noncomputable section

/-! The actual constructed Rees comparison is étale over every étale affine ambient chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalReducedReesComparison_pointed_etale_open
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (R : CommRingCat) [_root_.IsReduced R]
    (q : Spec R ⟶ X) [Etale q] (A : Ideal R) (hA : I.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel A) (a : A)
    (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart A a)) :
    ∃ (S : CommRingCat) (j : Spec S ⟶ Spec (.of (Blowup.Charts.Construction.blowupChart A a))), IsOpenImmersion j ∧
      (∃ P : PrimeSpectrum S, j P = p) ∧ Etale (j ≫ ReducedReesComparison.Construction.globalReducedReesComparison I hI R q A hA a) := by
  obtain ⟨U, S, φ, ψ, hopen, hψ, hcomm, Q, hQ⟩ :=
    Pointed.EtaleAffineFactorization.Construction.exists_pointed_etale_affine_factorization R q (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants A a) p)
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := hopen
  let : AlgebraicGeometry.IsReduced (Spec S) := isReduced_of_isOpenImmersion (Spec.map (CommRingCat.ofHom φ))
  let : _root_.IsReduced S := (affine_isReduced_iff S).mp inferInstance
  have hφ : φ.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance
  obtain ⟨P, hP, _⟩ := Blowup.ChartOpenBaseChange.Construction.exists_blowupChartMap_prime A a φ hφ p Q hQ
  let aS : A.map φ := ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩
  let j := Spec.map (CommRingCat.ofHom (ChartLift.Construction.blowupChartMap A φ a))
  let : IsOpenImmersion j := Blowup.ChartOpenBaseChange.Construction.blowupChartMap_isOpenImmersion A a φ
  have hS : I.comap (Spec.map (CommRingCat.ofHom φ) ≫ q) = Affine.QuotientKernel.Construction.affineQuotientKernel (A.map φ) := by
    rw [Scheme.IdealSheafData.comap_comp, hA, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  refine ⟨.of (Blowup.Charts.Construction.blowupChart (A.map φ) aS), j, inferInstance, ⟨P, hP⟩, ?_⟩
  have he := ReducedReesComparison.Construction.globalReducedReesComparison_refinement I hI R S q A hA a φ hS
  change Etale (Spec.map (CommRingCat.ofHom (ChartLift.Construction.blowupChartMap A φ a)) ≫
    ReducedReesComparison.Construction.globalReducedReesComparison I hI R q A hA a)
  rw [he]
  exact ReducedReesComparison.Construction.globalReducedReesComparison_etale_of_factorization I hI S _ (A.map φ) hS aS U ψ hψ hcomm

theorem globalReducedReesComparison_etale
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (R : CommRingCat) [_root_.IsReduced R]
    (q : Spec R ⟶ X) [Etale q] (A : Ideal R) (hA : I.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel A) (a : A) :
    Etale (ReducedReesComparison.Construction.globalReducedReesComparison I hI R q A hA a) := by
  choose S j hopen hpoint he using globalReducedReesComparison_pointed_etale_open I hI R q A hA a
  choose P hP using hpoint
  let : ∀ p, IsOpenImmersion (j p) := hopen
  let C : (Spec (.of (Blowup.Charts.Construction.blowupChart A a))).OpenCover :=
    Scheme.Cover.mkOfCovers _ (fun p => Spec (S p)) j (fun p => ⟨p, P p, hP p⟩) hopen
  let : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Etale)
  exact IsZariskiLocalAtSource.of_openCover (P := @Etale) C he

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.ReducedReesEtale.Construction
