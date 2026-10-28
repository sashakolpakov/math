import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleTensor
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Graph Polarization Powers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GraphPolarizationPowers.GraphPolarization

noncomputable section

/-! A fixed pullback-power identity fixes all line bundles on the graph
induced by the product polarization. This gives exact tensor-power
comparisons before passage to Hilbert polynomials. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleTensor.PolarizationAmpleness

universe u

variable {S : Scheme.{u}} (X : Over S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)

def graph (f : X ⟶ X) : X ⟶ X ⊗ X := lift (𝟙 X) f

theorem graph_fst (f : X ⟶ X) : graph X f ≫ fst X X = 𝟙 X := lift_fst _ _

theorem graph_snd (f : X ⟶ X) : graph X f ≫ snd X X = f := lift_snd _ _

theorem graph_closed [IsSeparated X.hom] (f : X ⟶ X) :
    IsClosedImmersion (graph X f).left := by
  have h : (graph X f).left ≫ (fst X X).left = 𝟙 X.left :=
    congrArg Over.Hom.left (graph_fst X f)
  have : IsClosedImmersion ((graph X f).left ≫ (fst X X).left) := by
    rw [h]
    infer_instance
  have : IsSeparated (fst X X).left :=
    inferInstanceAs (IsSeparated (CategoryTheory.Limits.pullback.fst X.hom X.hom))
  exact IsClosedImmersion.of_comp (graph X f).left (fst X X).left

def productLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (X ⊗ X).left :=
  (L.pullback (fst X X).left).tensor (L.pullback (snd X X).left)

theorem graph_product_class (f : X ⟶ X) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (graph X f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (productLine X L)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L * Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
  have hf : (graph X f).left ≫ (fst X X).left = 𝟙 X.left :=
    congrArg Over.Hom.left (graph_fst X f)
  have hs : (graph X f).left ≫ (snd X X).left = f.left :=
    congrArg Over.Hom.left (graph_snd X f)
  change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (graph X f).left
    (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst X X).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd X X).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
  rw [map_mul]
  have h₁ := (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (graph X f).left (fst X X).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
    ((congrArg (fun a => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) hf).trans
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)))
  have h₂ := (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (graph X f).left (snd X X).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
    (congrArg (fun a => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) hs)
  exact congrArg₂ (fun a b : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.left => a * b) h₁ h₂

variable (f : X ⟶ X) (n : ℕ)
  (hf : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ n)

include hf in
theorem graph_product_power_class (r : ℕ) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (graph X f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (productLine X (L.tensorPower r))) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ ((n + 1) * r) := by
  rw [graph_product_class, AmpleTensor.PolarizationAmpleness.tensorPower_class, map_pow, hf, ← mul_pow, ← pow_succ', ← pow_mul]

include hf in
/-- Every graph power is the same fixed power on the source. Thus its
sections and higher cohomology are independent of the chosen similitude. -/
theorem graph_tensor_power_iso (r m : ℕ) : Nonempty
    ((((productLine X (L.tensorPower r)).tensorPower m).pullback (graph X f).left).sheaf ≅
      (L.tensorPower (((n + 1) * r) * m)).sheaf) := by
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf
        (((productLine X (L.tensorPower r)).tensorPower m).pullback (graph X f).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower (((n + 1) * r) * m)) := by
    change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (graph X f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((productLine X (L.tensorPower r)).tensorPower m)) = _
    rw [AmpleTensor.PolarizationAmpleness.tensorPower_class, map_pow, graph_product_power_class X L f n hf, ← pow_mul,
      AmpleTensor.PolarizationAmpleness.tensorPower_class]
  exact Quotient.exact h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GraphPolarizationPowers.GraphPolarization
