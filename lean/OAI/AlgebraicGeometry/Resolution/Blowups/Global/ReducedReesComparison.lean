import OAI.AlgebraicGeometry.Resolution.Blowups.AffineGlobalBlowupLift
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.IdealReesComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.BaseChangeCharts

/-! # Reduced Rees Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.ReducedReesComparison.Construction

noncomputable section

section

/-! Actual Rees-chart comparison maps into a global blowup, with reduced affine chart rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem rees_comparison_center_pullback
    {X : Scheme.{0}} (I : X.IdealSheafData) (R : CommRingCat.{0}) (q : Spec R ⟶ X)
    (A : Ideal R) (hA : I.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel A) (a : A) :
    I.comap (Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants A a)) ≫ q) =
      Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {Blowup.Charts.Construction.blowupChartConstants A a a.val}) := by
  rw [Scheme.IdealSheafData.comap_comp, hA, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, ExceptionalIdeal.Construction.blowupChart_extendedIdeal]

def globalReducedReesComparison
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (R : CommRingCat.{0}) [_root_.IsReduced R]
    (q : Spec R ⟶ X) (A : Ideal R) (hA : I.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel A) (a : A) :
    Spec (.of (Blowup.Charts.Construction.blowupChart A a)) ⟶ GlobalBlowup.Data.Construction.globalBlowup I hI :=
  AffineGlobalBlowupLift.Construction.reducedAffineGlobalBlowupLift I hI (.of (Blowup.Charts.Construction.blowupChart A a))
    (Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants A a)) ≫ q)
    (Blowup.Charts.Construction.blowupChartConstants A a a.val) (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular A a)
    (rees_comparison_center_pullback I R q A hA a)

theorem globalReducedReesComparison_over
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (R : CommRingCat.{0}) [_root_.IsReduced R]
    (q : Spec R ⟶ X) (A : Ideal R) (hA : I.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel A) (a : A) :
    globalReducedReesComparison I hI R q A hA a ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI =
      Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants A a)) ≫ q :=
  AffineGlobalBlowupLift.Construction.reducedAffineGlobalBlowupLift_over I hI (.of (Blowup.Charts.Construction.blowupChart A a)) _ _ _ _

theorem globalReducedReesComparison_unique
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (R : CommRingCat.{0}) [_root_.IsReduced R]
    (q : Spec R ⟶ X) (A : Ideal R) (hA : I.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel A) (a : A)
    (g : Spec (.of (Blowup.Charts.Construction.blowupChart A a)) ⟶ GlobalBlowup.Data.Construction.globalBlowup I hI)
    (hg : g ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI = Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants A a)) ≫ q) :
    g = globalReducedReesComparison I hI R q A hA a :=
  (AffineGlobalBlowupLift.Construction.existsUnique_globalBlowup_lift_reduced_affine I hI (.of (Blowup.Charts.Construction.blowupChart A a)) _
    (Blowup.Charts.Construction.blowupChartConstants A a a.val) (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular A a)
    (rees_comparison_center_pullback I R q A hA a)).choose_spec.2 g hg

theorem globalReducedReesComparison_controlledIdeal
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ) (hp : J ≤ I ^ b)
    (R : CommRingCat.{0}) [_root_.IsReduced R] (q : Spec R ⟶ X) (A B : Ideal R)
    (hA : I.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel A) (hB : J.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel B) (a : A) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap (globalReducedReesComparison I hI R q A hA a) =
      Affine.QuotientKernel.Construction.affineQuotientKernel (ControlledTransform.Construction.blowupControlledTransform A B b a) :=
  GlobalControlled.IdealReesComparison.Construction.globalBlowupControlledIdeal_comap_rees_comparison I J hI b hp R q A B hA hB a _
    (globalReducedReesComparison_over I hI R q A hA a)

end

/-! Constructed reduced Rees comparisons agree with native base-change charts and commute with refinement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalReducedReesComparison_eq_baseChange
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (U : X.affineOpens)
    (R : CommRingCat) [_root_.IsReduced R] (φ : Γ(X, U) →+* R)
    (hA : I.comap (Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec) =
      Affine.QuotientKernel.Construction.affineQuotientKernel ((I.ideal U).map φ)) (a : (I.ideal U).map φ) :
    globalReducedReesComparison I hI R (Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec)
      ((I.ideal U).map φ) hA a = GlobalControlled.BaseChangeCharts.Construction.globalBlowupBaseChangeReesChart I hI U φ a := by
  symm
  apply globalReducedReesComparison_unique
  rw [GlobalControlled.BaseChangeCharts.Construction.globalBlowupBaseChangeReesChart_over, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem globalReducedReesComparison_etale_of_factorization
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (R : CommRingCat) [_root_.IsReduced R]
    (q : Spec R ⟶ X) (A : Ideal R) (hA : I.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel A) (a : A)
    (U : X.affineOpens) (φ : Γ(X, U) →+* R) (hφ : φ.Etale)
    (hq : q = Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec) :
    Etale (globalReducedReesComparison I hI R q A hA a) := by
  subst q
  have he : A = (I.ideal U).map φ := by
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
    exact hA.symm.trans (Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel I U φ)
  subst A
  rw [globalReducedReesComparison_eq_baseChange]
  exact GlobalControlled.BaseChangeCharts.Construction.globalBlowupBaseChangeReesChart_etale I hI U φ hφ a

theorem globalReducedReesComparison_refinement
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (R S : CommRingCat) [_root_.IsReduced R] [_root_.IsReduced S]
    (q : Spec R ⟶ X) (A : Ideal R) (hA : I.comap q = Affine.QuotientKernel.Construction.affineQuotientKernel A) (a : A)
    (φ : R →+* S)
    (hS : I.comap (Spec.map (CommRingCat.ofHom φ) ≫ q) = Affine.QuotientKernel.Construction.affineQuotientKernel (A.map φ)) :
    Spec.map (CommRingCat.ofHom (ChartLift.Construction.blowupChartMap A φ a)) ≫ globalReducedReesComparison I hI R q A hA a =
      globalReducedReesComparison I hI S (Spec.map (CommRingCat.ofHom φ) ≫ q)
        (A.map φ) hS ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩ := by
  apply globalReducedReesComparison_unique
  rw [Category.assoc, globalReducedReesComparison_over]
  have hring : (ChartLift.Construction.blowupChartMap A φ a).comp (Blowup.Charts.Construction.blowupChartConstants A a) =
      (Blowup.Charts.Construction.blowupChartConstants (A.map φ) ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩).comp φ :=
    RingHom.ext (ChartLift.Construction.blowupChartMap_constants A φ a)
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun v : R →+* Blowup.Charts.Construction.blowupChart (A.map φ) ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩ =>
    Spec.map (CommRingCat.ofHom v) ≫ q) hring

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.ReducedReesComparison.Construction
