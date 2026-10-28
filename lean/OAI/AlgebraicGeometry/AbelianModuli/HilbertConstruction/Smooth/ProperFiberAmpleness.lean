import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProperNoetherianDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.NoetherianLineModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.NoetherianModelRecovery

/-! # Proper Fiber Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProperFiberAmpleness

noncomputable section

/-! Fiberwise ampleness on a smooth proper family over an arbitrary
affine base gives ampleness on the original family. Both the scheme
and its line bundle have actual finite-coefficient models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines

theorem smoothProper_isAmple_of_fiberwise
    {R : Type} [CommRing R] (X : Over (Spec (.of R)))
    [Smooth X.hom] [IsProper X.hom] (L : Line.Bundles.LineBundle X.left)
    (hL : ∀ x : Spec (.of R), (L.pullback (X.hom.fiberι x)).IsAmple) :
    L.IsAmple := by
  obtain ⟨C, hC, hCN, Y, hYs, hYp, q, hq⟩ :=
    ProperNoetherianDescent.exists_smooth_proper_noetherian_scheme_model X
  have : Algebra.FiniteType ℤ C := hC
  have : IsNoetherianRing C := hCN
  have : Smooth Y.hom := hYs
  have : IsProper Y.hom := hYp
  obtain ⟨s, K, a, ha, ⟨eK⟩⟩ :=
    Cartesian.NoetherianLineModel.exists_finiteType_cartesian_line_model C R X Y q hq L
  let T := Spec (.of (ReferenceFamily.Finite.CoefficientDiagram.finiteCoefficientRing C R s))
  let Y₁ := (Over.pullback (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.stageBase C R s)).obj Y
  have : IsProper Y₁.hom :=
    inferInstanceAs (IsProper (pullback.snd Y.hom (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.stageBase C R s)))
  have : Flat Y₁.hom :=
    inferInstanceAs (Flat (pullback.snd Y.hom (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.stageBase C R s)))
  have : IsNoetherianRing Γ(T, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsAffineHom (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.stageProjection C R s) :=
    isAffineHom_of_isAffine (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.stageProjection C R s)
  exact Ample.NoetherianModelRecovery.isAmple_of_noetherian_model X.hom Y₁.hom a (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.stageProjection C R s)
    ha L K eK hL

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProperFiberAmpleness
