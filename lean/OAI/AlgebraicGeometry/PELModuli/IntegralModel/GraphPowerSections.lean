import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GraphPolarizationPowers

/-! # Graph Power Sections -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GraphPowerSections.GraphPolarization

noncomputable section

/-! The graph power comparisons induce linear isomorphisms on the actual
global-section modules, before any numerical Hilbert-function comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {S : Scheme.{u}} (X : Over S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (f : X ⟶ X) (n : ℕ)
  (hf : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ n)
  (r m : ℕ)

def graphPowerIso :
    (((GraphPolarizationPowers.GraphPolarization.productLine X (L.tensorPower r)).tensorPower m).pullback (GraphPolarizationPowers.GraphPolarization.graph X f).left).sheaf ≅
      (L.tensorPower (((n + 1) * r) * m)).sheaf :=
  Classical.choice (GraphPolarizationPowers.GraphPolarization.graph_tensor_power_iso X L f n hf r m)

def graphPowerSectionsLinearEquiv :
    Γ((((GraphPolarizationPowers.GraphPolarization.productLine X (L.tensorPower r)).tensorPower m).pullback (GraphPolarizationPowers.GraphPolarization.graph X f).left).sheaf, ⊤) ≃ₗ[Γ(X.left, ⊤)]
      Γ((L.tensorPower (((n + 1) * r) * m)).sheaf, ⊤) :=
  ((SheafOfModules.evaluation (R := X.left.ringCatSheaf) (op ⊤)).mapIso
    (graphPowerIso X L f n hf r m)).toLinearEquiv

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GraphPowerSections.GraphPolarization
