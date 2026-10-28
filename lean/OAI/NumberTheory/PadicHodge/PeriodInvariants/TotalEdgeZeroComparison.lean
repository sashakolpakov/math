import OAI.NumberTheory.PadicHodge.PeriodInvariants.ModuleTotalEdgeComparison
import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaQuasiIsomorphisms

/-! # Total Edge Zero Comparison -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.TotalEdgeZeroComparison

noncomputable section

/-! # Degree zero of the actual first-quadrant edge comparison -/

open _root_.CategoryTheory Limits _root_.HomologicalComplex₂ OAI.NumberTheory.PadicHodge.PeriodInvariants.ModuleHomologyMaps

universe u
variable {R : Type u} [CommRing R]
  (K : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ))
  (A : CochainComplex (ModuleCat.{u} R) ℕ)
  (e : ∀ q, A.X q ⟶ (K.X q).X 0)
  (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
    e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
  (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)

local notation "f" => (OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K) A e he w

theorem edge_projection (a : A.X 0) : ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) 0 0 0).hom ((f).f 0 a) = e 0 a := by
  have h : (f).f 0 ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) 0 0 0 = e 0 := by
    change (e 0 ≫ K.ιTotal (.up ℕ) 0 0 0 rfl) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) 0 0 0 = e 0
    rw [Category.assoc, (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat_self K) 0 0, Category.comp_id]
  exact congrArg (fun g => g.hom a) h

variable (haug : (ShortComplex.mk (e 0) ((K.X 0).d 0 1) (w 0)).Exact)
  [he₀ : Mono (e 0)] [he₁ : Mono (e 1)]

include haug in
theorem zero_cycle_bijective :
    Function.Bijective (ModuleHomologyMaps.cycleMap (EtaQuasiIsomorphisms.zeroShortMap f)) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (ModuleCat.mono_iff_injective (e 0)).mp inferInstance
    have hv := congrArg (fun z => ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) 0 0 0).hom z.val) hxy
    exact (edge_projection K A e he w x.val).symm.trans
      (hv.trans (edge_projection K A e he w y.val))
  · intro y
    let x := ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) 0 0 0).hom y.val
    have hx₁ : ((K.X 0).d 0 1).hom x = 0 := by
      have h := congrArg (fun g => g.hom y.val) (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_zero K 0)
      have hy : ((K.total (.up ℕ)).d 0 1).hom y.val = 0 := y.property
      exact h.symm.trans ((congrArg ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) 0 1 1).hom hy).trans (map_zero _))
    have hx₂ : ((K.d 0 1).f 0).hom x = 0 := by
      have h := congrArg (fun g => g.hom y.val) (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_zero_right K 0)
      have hy : ((K.total (.up ℕ)).d 0 1).hom y.val = 0 := y.property
      exact h.symm.trans ((congrArg ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) 1 0 1).hom hy).trans (map_zero _))
    obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp haug x hx₁
    have ha' : (e 0).hom a = x := ha
    have haCycle : (A.d 0 1).hom a = 0 := by
      apply (ModuleCat.mono_iff_injective (e 1)).mp inferInstance
      rw [map_zero]
      have h := congrArg (fun g => g.hom a) (he 0 1 rfl)
      exact h.symm.trans ((congrArg ((K.d 0 1).f 0).hom ha').trans hx₂)
    refine ⟨⟨a, haCycle⟩, ?_⟩
    apply Subtype.ext
    have h := congrArg (fun g => g.hom y.val) ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.totalUpNat_zero_decomposition K))
    exact (congrArg (K.ιTotal (.up ℕ) 0 0 0 rfl).hom ha').trans h

include haug in
theorem horizontal : QuasiIsoAt f 0 :=
  (EtaQuasiIsomorphisms.quasiIsoAt_zero_iff f).mpr (zero_cycle_bijective K A e he w haug)

variable (B : CochainComplex (ModuleCat.{u} R) ℕ)
  (v : ∀ p, B.X p ⟶ (K.X 0).X p)
  (hv : ∀ p p', (ComplexShape.up ℕ).Rel p p' →
    v p ≫ (K.X 0).d p p' = B.d p p' ≫ v p')
  (wv : ∀ p, v p ≫ (K.d 0 1).f p = 0)
  (haugv : (ShortComplex.mk (v 0) ((K.d 0 1).f 0) (wv 0)).Exact)
  [hv₀ : Mono (v 0)] [hv₁ : Mono (v 1)]

omit he₀ he₁ in
include haugv hv₀ hv₁ in
theorem vertical : QuasiIsoAt ((AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge.HomologicalComplex₂.totalUpNatVerticalEdge K) B v hv wv) 0 := by
  have : QuasiIsoAt ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K.flip) B v hv wv) 0 :=
    @horizontal R _ K.flip B v hv wv haugv hv₀ hv₁
  change QuasiIsoAt ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K.flip) B v hv wv ≫ (K.totalFlipIso (.up ℕ)).hom) 0
  infer_instance

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.TotalEdgeZeroComparison
