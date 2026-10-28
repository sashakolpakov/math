import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AdelicBinaryClosure
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RotatedActiveDensity
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InducedProductClosure
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InducedProductCompatibility

/-! # Induced Away Density -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.InducedAwayDensity.Approximation

noncomputable section

/-! Density in an actual rational away range with its induced unitary
topology follows from supported quaternion approximation and the fixed
rational positive rotation. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {q : ℕ} [Fact q.Prime] (σ : E →+* Padic q)
  (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  (places : HeckeCycles.GeometricSource.CM.Places E)
  {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  (r : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b →* Matrix.SpecialLinearGroup (Fin 3) (Padic q) × A)
  (p : A →* AdelicBinaryClosure.Approximation.CMHermitianAway E σ b hb hb0 δ hδ)

theorem cm_induced_away_density
    (hball : (HeckeCycles.ReferenceDatum.CM.embeddings E places places.distinguished b).re < 0)
    (hp : Topology.IsInducing p)
    (hcompat : ∀ g, Prod.map id p (r g) = AdelicBinaryClosure.Approximation.cmActiveAwayRational E σ b hb hb0 δ hδ hδ0 g)
    (haway : Function.Surjective (fun g => (r g).2)) : DenseRange r := by
  have hbinary (B : Matrix.SpecialLinearGroup (Fin 2) (Padic q)) :
      (Quaternion.QuadraticUnitary.activeBinaryBlock B, (1 : A)) ∈ r.range.topologicalClosure :=
    InducedProductCompatibility.Approximation.compatible_induced_supported_closure p r (AdelicBinaryClosure.Approximation.cmActiveAwayRational E σ b hb hb0 δ hδ hδ0)
      hcompat hp (Quaternion.QuadraticUnitary.activeBinaryBlock B) (AdelicBinaryClosure.Approximation.cm_binary_mem_closure E σ b hb hb0 δ hδ hδ0 places hball B)
  let γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b := ActiveRotation.Approximation.positiveRotationUnitary E (IsCMField.complexConj E).toRingHom b
  have hγ : (r γ).1 = ActiveRotation.Approximation.positiveRotation (Padic q) :=
    (InducedProductCompatibility.Approximation.product_compatibility_first p r (AdelicBinaryClosure.Approximation.cmActiveAwayRational E σ b hb hb0 δ hδ hδ0) hcompat γ).trans
      ((AdelicBinaryClosure.Approximation.cmActiveAwayRational_first E σ b hb hb0 δ hδ hδ0 γ).trans (ActiveRotation.Approximation.positiveRotation_map E σ))
  apply RotatedActiveDensity.Approximation.denseRange_product_of_binary_and_rotation r haway γ hγ
  · intro x
    simpa only [ActiveRotation.Approximation.activeBinaryBlock_forward] using
      hbinary (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) x)
  · intro x
    simpa only [ActiveRotation.Approximation.activeBinaryBlock_backward] using
      hbinary (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.InducedAwayDensity.Approximation
