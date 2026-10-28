import OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice

/-! # Source Fixed Form -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SourceFixedForm.TestTransport

noncomputable section

/-! A fixed source test gives exact covariance of its actual theta one-form. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

variable {F : Type} [Field F] [NumberField F] {d : F}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {K : (Matrix (Fin 1) (Fin 1) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d 1 H K}

theorem source_fixed_form_covariance (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A)
    (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K) (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 1)
    (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 1 H K hd C P)
    (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B) (hCovariance : RepresentationTheory.Theta.Adelic.DataTheta.Descent.RationalHeckeCovariance B P hd C D)
    (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val) (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1))
    (hfixed : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction F H K hd C P D (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H g) f = f) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    (RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B f (B.ball (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU F H g) • z)).comp
      (fderiv ℂ (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage
        (RepresentationTheory.Theta.Adelic.BallNatural.asSL (B.ball (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val) = RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B f z := by
  apply ContinuousLinearMap.ext
  intro u
  have h := RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicCovariance.thetaOneForm_covariance B P hd C D hGeometry hCovariance g f z u
  rwa [hfixed] at h

theorem covector_invariance_of_scalar_comparison {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (f g f' g' : V →L[ℂ] W) (D : V →L[ℂ] V) (c : ℂ) (hc : c ≠ 0)
    (hf : f = c • f') (hg : g = c • g') (h : f.comp D = g) : f'.comp D = g' := by
  rw [hf, hg, ContinuousLinearMap.smul_comp] at h
  exact (smul_right_injective _ hc) h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SourceFixedForm.TestTransport
