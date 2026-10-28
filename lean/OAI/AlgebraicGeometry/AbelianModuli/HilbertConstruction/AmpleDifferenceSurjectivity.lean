import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferenceTwistFieldVanishing

/-! # Ample Difference Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmpleDifferenceSurjectivity.Theta.Geometric

noncomputable section

/-! An ample line on a projective abelian variety realizes every
homogeneous line by translation, in every characteristic. A missed line
would make all the twisted difference cohomology vanish, contradicting
the nonzero Euler characteristic of a suitable positive tensor power. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferenceTwistFieldVanishing

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of k))) (L N : Line.Bundles.LineBundle A.scheme.left)

theorem algebraic_ampleDifference_realizes_homogeneous_line
    (hL : L.IsAmple) (hN : ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf N)) :
    Picard.ThetaConstruction.DifferenceParameterTransport.Geometric.HasDifferenceParameter A L N := by
  by_contra hne
  let P := hL.projectivePresentation A.scheme.hom
  obtain ⟨m, _, hm⟩ := DifferenceTwistEuler.differenceTwistedLine_exists_nonzero_euler A L hL N.reciprocalFrameBundle
  apply hm
  let F := DifferenceTwistEuler.differenceTwistedLine A (L.tensorPower m) N.reciprocalFrameBundle
  have hv (q : ℕ) : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H F.sheaf q) :=
    DifferenceTwistFieldVanishing.differenceTwistedLine_cohomology_vanish_of_no_parameter A P L N hN hne m q
  rw [External.AcyclicEuler.coefficientEulerCharacteristic_eq_finrank_zero (A.scheme ⊗ A.scheme).hom F.sheaf
    (fun q => hv (q + 1))]
  have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap (A.scheme ⊗ A.scheme).hom) 0).obj F.sheaf) := hv 0
  simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmpleDifferenceSurjectivity.Theta.Geometric
