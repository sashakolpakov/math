import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleChernPositive
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveFormAverage
import OAI.AlgebraicGeometry.AbelianVariety.PureAverage

/-! # Ample Chern Invariant -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleChernInvariant

noncomputable section

section

/-! The actual ample Chern class admits a real, strictly positive,
translation-invariant (1,1) representative on the native abelian variety. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology _root_.MeasureTheory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

theorem ampleChern_invariant_representative (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple) :
    ∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms A.variety.analyticModel A.variety.analyticSpace 2,
      a.val ∈ AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := A.variety.analyticModel) (G := A.variety.analyticSpace) 2 ∧
      (A.variety.deRhamBettiIso 2).hom (A.variety.deRhamClass 2 a) =
        A.variety.rationalCohomologyInclusion 2 (Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L) ∧
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree A.variety.analyticModel A.variety.analyticSpace 1 1 a.val.val ∧
      (∀ (x : A.variety.analyticSpace) (u : TangentSpace 𝓘(ℝ, A.variety.analyticModel) x), u ≠ 0 →
        0 < (a.val x ![u, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I u]).re) ∧
      ∀ (x : A.variety.analyticSpace) (v : Fin 2 → TangentSpace 𝓘(ℝ, A.variety.analyticModel) x),
        (a.val x v).im = 0 := by
  obtain ⟨a, ha, ht, hp, hr⟩ := AmpleChernPositive.ampleChern_positive_representative A.variety L hL
  let : MeasurableSpace A.variety.analyticSpace := borel _
  let : BorelSpace A.variety.analyticSpace := ⟨rfl⟩
  let : ConnectedSpace A.variety.analyticSpace := AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPoint_connectedSpace A
  let haar := AbelianVariety.Averaging.Constructions.ExteriorCohomology.compactGroupHaar (E := A.variety.analyticModel) (G := A.variety.analyticSpace)
  let b := AbelianVariety.CyclePeriods.Constructions.ExteriorCohomology.averageClosedForm (E := A.variety.analyticModel) (G := A.variety.analyticSpace) haar 2 a
  have hb := AbelianVariety.Averaging.Constructions.ExteriorCohomology.averageForms_mem (E := A.variety.analyticModel) (G := A.variety.analyticSpace) haar a.val
  have hbtype := AbelianVariety.PureAverage.Constructions.ExteriorCohomology.averageForms_pure (E := A.variety.analyticModel) (G := A.variety.analyticSpace)
    (p := 1) (q := 1) haar a.val ht
  have hbpos := PositiveFormAverage.averageForms_positive (E := A.variety.analyticModel) (G := A.variety.analyticSpace)
    haar a.val hp
  have hbreal := PositiveFormAverage.averageForms_real (E := A.variety.analyticModel) (G := A.variety.analyticSpace)
    haar a.val hr
  refine ⟨b, hb, ?_, hbtype, hbpos, hbreal⟩
  exact (congrArg (fun b => (A.variety.deRhamBettiIso 2).hom b)
    (AbelianVariety.CyclePeriods.Constructions.ExteriorCohomology.averageClosedForm_deRhamClass (E := A.variety.analyticModel) (G := A.variety.analyticSpace) haar a)).trans ha

end

/-! The canonical integration-normalized invariant covector of the
actual ample Chern class is real, positive, and nondegenerate. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

theorem abelianCovectorBettiEquiv_invariant (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms A.variety.analyticModel A.variety.analyticSpace n)
    (ha : a.val ∈ AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms n) :
    AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A n (a.val 1) = (A.variety.deRhamBettiIso n).hom (A.variety.deRhamClass n a) := by
  let b : AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := A.variety.analyticModel) (G := A.variety.analyticSpace) n := ⟨a.val, ha⟩
  have h := (AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantFormsEvalEquiv (E := A.variety.analyticModel) (G := A.variety.analyticSpace) n).symm_apply_apply b
  exact congrArg (fun c => (A.variety.deRhamBettiIso n).hom (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianInvariantDeRhamEquiv A n c)) h

def nativeChernCovector (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) :
    A.variety.analyticModel [⋀^Fin 2]→L[ℝ] ℂ :=
  (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A 2).symm
    (A.variety.rationalCohomologyInclusion 2 (Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L))

theorem nativeChernCovector_eq (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms A.variety.analyticModel A.variety.analyticSpace 2)
    (ha : a.val ∈ AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms 2)
    (hc : (A.variety.deRhamBettiIso 2).hom (A.variety.deRhamClass 2 a) =
      A.variety.rationalCohomologyInclusion 2 (Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L)) :
    nativeChernCovector A L = a.val 1 := by
  apply (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A 2).injective
  exact (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A 2).apply_symm_apply _ |>.trans
    (hc.symm.trans (abelianCovectorBettiEquiv_invariant A 2 a ha).symm)

theorem nativeChernCovector_positive (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : L.IsAmple) (u : A.variety.analyticModel) (hu : u ≠ 0) :
    0 < (nativeChernCovector A L ![u,
      Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul (1 : A.variety.analyticSpace) Complex.I u]).re := by
  obtain ⟨a, ha, hc, _ht, hp, _hr⟩ := ampleChern_invariant_representative A L hL
  have he := congrArg (fun c : A.variety.analyticModel [⋀^Fin 2]→L[ℝ] ℂ =>
    (c ![u, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul (1 : A.variety.analyticSpace) Complex.I u]).re)
      (nativeChernCovector_eq A L a ha hc)
  exact he.symm ▸ hp 1 u hu

theorem nativeChernCovector_real (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : L.IsAmple) (v : Fin 2 → A.variety.analyticModel) : (nativeChernCovector A L v).im = 0 := by
  obtain ⟨a, ha, hc, _ht, _hp, hr⟩ := ampleChern_invariant_representative A L hL
  exact (congrArg (fun c : A.variety.analyticModel [⋀^Fin 2]→L[ℝ] ℂ => (c v).im)
    (nativeChernCovector_eq A L a ha hc)).trans (hr 1 v)

theorem nativeChernCovector_positive_model (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : L.IsAmple) (u : A.variety.analyticModel) (hu : u ≠ 0) :
    0 < (nativeChernCovector A L ![u, Complex.I • u]).re := by
  have h := nativeChernCovector_positive A L hL u hu
  have he := Holomorphic.TangentMaps.complexTangentSMul_model (1 : A.variety.analyticSpace) Complex.I u
  exact (congrArg (fun v => (nativeChernCovector A L ![u, v]).re) he) ▸ h

theorem nativeChernCovector_pure (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : L.IsAmple) : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree A.variety.analyticModel 1 1 (nativeChernCovector A L) := by
  obtain ⟨a, ha, hc, ht, _hp, _hr⟩ := ampleChern_invariant_representative A L hL
  let e := chartAt A.variety.analyticModel (1 : A.variety.analyticSpace)
  have he : e ∈ atlas A.variety.analyticModel A.variety.analyticSpace := chart_mem_atlas _ _
  have hx : (1 : A.variety.analyticSpace) ∈ e.source := mem_chart_source _ _
  have hv : a.val.val.inChart e (e 1) = a.val 1 := by
    ext v
    exact (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at a.val.val e he 1 hx v).trans
      (congrArg (a.val 1) (funext (fun i => Holomorphic.TangentMaps.preferredTangent_inverse_identity (1 : A.variety.analyticSpace) (v i))))
  have hb : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree A.variety.analyticModel 1 1 (a.val 1) := hv ▸ ht e he (e 1) (e.map_source hx)
  exact (nativeChernCovector_eq A L a ha hc).symm ▸ hb

theorem nativeChernCovector_separating (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : L.IsAmple) (u : A.variety.analyticModel)
    (hu : ∀ v, nativeChernCovector A L ![u, v] = 0) : u = 0 := by
  by_contra hn
  have h := nativeChernCovector_positive A L hL u hn
  have hz := congrArg Complex.re (hu (Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul (1 : A.variety.analyticSpace) Complex.I u))
  exact (ne_of_gt h) hz

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleChernInvariant
