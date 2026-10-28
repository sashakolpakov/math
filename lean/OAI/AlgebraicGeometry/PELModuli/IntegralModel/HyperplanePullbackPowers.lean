import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicProjectivePowers

/-! # Hyperplane Pullback Powers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.HyperplanePullbackPowers

noncomputable section

/-! A native hyperplane pullback isomorphism determines all native
projective twist pullbacks, via the actual line-bundle tensor powers. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}
  (a : X ⟶ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).left) (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
  (j : Fin (n + 1))

theorem hyperplane_pullback_power_iso
    (he : Nonempty ((Scheme.Modules.pullback a).obj
      (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) ≅ P.sheaf)) (m : ℕ) :
    Nonempty ((Scheme.Modules.pullback a).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m) ≅ (P.tensorPower m).sheaf) := by
  have hc : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Projective.HyperplanePowers.PolarizationEmbedding.projectiveHyperplaneLine R n j)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P := Quotient.sound he
  have hp : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (((Projective.HyperplanePowers.PolarizationEmbedding.projectiveHyperplaneLine R n j).tensorPower m).pullback a) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (P.tensorPower m) := by
    change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback a
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((Projective.HyperplanePowers.PolarizationEmbedding.projectiveHyperplaneLine R n j).tensorPower m)) = _
    rw [AmpleTensor.PolarizationAmpleness.tensorPower_class, map_pow, hc, AmpleTensor.PolarizationAmpleness.tensorPower_class]
  obtain ⟨e⟩ := Quotient.exact hp
  exact ⟨(Scheme.Modules.pullback a).mapIso (IntrinsicProjectivePowers.PolarizationEmbedding.nativeHyperplanePowerIso R n j m) ≪≫ e⟩

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.HyperplanePullbackPowers
