import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ConstantSections
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointHomotopy
import OAI.AlgebraicGeometry.Betti.Scheme

/-! # Section Betti -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.SectionBetti.BundleCycles

noncomputable section

/-! The actual algebraic zero and one sections induce identical Betti
pullbacks, by the constructed homotopy on ordinary complex points. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineLineConstantSectionOver_pointMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a : ℂ) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (ConstantSections.BundleCycles.affineLineConstantSectionOver X a) = PointHomotopy.BundleCycles.affineLinePointSection X a := by
  ext x
  exact (ConstantSections.BundleCycles.affineLinePointFamily_eq_constantSection X a x).symm

theorem affineLineConstantSections_betti_eq (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    {R : Type} [Ring R] (M : ModuleCat.{0} R) (n : ℕ) :
    Betti.Scheme.schemeBettiMap M n (ConstantSections.BundleCycles.affineLineConstantSectionOver X 0) =
      Betti.Scheme.schemeBettiMap M n (ConstantSections.BundleCycles.affineLineConstantSectionOver X 1) := by
  unfold Betti.Scheme.schemeBettiMap
  rw [affineLineConstantSectionOver_pointMap, affineLineConstantSectionOver_pointMap]
  exact PointHomotopy.BundleCycles.affineLinePointSections_cohomology_eq X M n

theorem affineLineFamily_endpoints_betti_eq {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : OverProduct.BundleCycles.affineLineOver X ⟶ Y)
    {R : Type} [Ring R] (M : ModuleCat.{0} R) (n : ℕ) :
    Betti.Scheme.schemeBettiMap M n (ConstantSections.BundleCycles.affineLineConstantSectionOver X 0 ≫ f) =
      Betti.Scheme.schemeBettiMap M n (ConstantSections.BundleCycles.affineLineConstantSectionOver X 1 ≫ f) := by
  have h₀ := (Betti.Scheme.schemeBettiFunctor M n).map_comp f.op (ConstantSections.BundleCycles.affineLineConstantSectionOver X 0).op
  have h₁ := (Betti.Scheme.schemeBettiFunctor M n).map_comp f.op (ConstantSections.BundleCycles.affineLineConstantSectionOver X 1).op
  exact h₀.trans ((congrArg (fun k => Betti.Scheme.schemeBettiMap M n f ≫ k)
    (affineLineConstantSections_betti_eq X M n)).trans h₁.symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.SectionBetti.BundleCycles
