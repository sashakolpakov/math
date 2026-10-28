import OAI.RepresentationTheory.Theta.Adelic.TensorOrbitSetoid
import OAI.RepresentationTheory.Theta.Adelic.DataTheta
import OAI.RepresentationTheory.Theta.Adelic.QuotientSection

/-! # Tensor Section Descent -/

namespace OAI.RepresentationTheory.Theta.Adelic.TensorSectionDescent

noncomputable section

/-! Actual symmetric geometric theta tensors descend to continuous
sections on every principal quotient whose finite level fixes the inputs. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.TensorOrbitSetoid
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.SymmetricGeometricTensor OAI.RepresentationTheory.Theta.Adelic.QuotientSection

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)
variable (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)

theorem tensor_sections_of_fixed_principal_level
    (hΘ : DataTheta.Descent.ThetaConstruction (GeometricGaussians.constructedComparison A P))
    (hHecke : DataTheta.Descent.RationalHeckeCovariance (GeometricGaussians.constructedComparison A P) P hd C D)
    (N : ℕ) (Γ : Subgroup (SpecialUnitary.SU H.val)) (hΓ : ∀ g, g ∈ Γ ↔ BallGeometryData.PrincipalLevel N g)
    (Φ : Finset (FiniteSchwartz.finiteSchwartz F (3 * m)))
    (hfix : ∀ f ∈ Φ, ∀ g : SpecialUnitary.SU H.val, BallGeometryData.PrincipalLevel N g →
      FiniteSchwartz.finiteAction F H K hd C P D (RationalSU.rationalFiniteSU F H g) f = f)
    (R : Setoid BallNatural.Ball)
    (hR : ∀ z w, R.r z w ↔ DataTheta.Descent.BallOrbit (GeometricGaussians.constructedComparison A P) N z w)
    (a : ℕ) :
    ∃ S : Setoid (BallNatural.Ball × DataTheta.Descent.SymmetricTensor (A := A) a),
      (∀ p q, S.r p q ↔ DataTheta.Descent.TensorOrbit (GeometricGaussians.constructedComparison A P) N a p q) ∧
      ∃ projection : Quotient S → Quotient R,
        Continuous projection ∧
        (∀ p, projection (Quotient.mk S p) = Quotient.mk R p.1) ∧
        ∀ f ∈ Φ, ∃ T : BallNatural.Ball → DataTheta.Descent.SymmetricTensor (A := A) a,
          (∀ z, (T z).val = DataTheta.geometricTensor (GeometricGaussians.constructedComparison A P) f a z) ∧
          ∃ descended : Quotient R → Quotient S,
            Continuous descended ∧
            (∀ q, projection (descended q) = q) ∧
            ∀ z, descended (Quotient.mk R z) = Quotient.mk S (z, T z) := by
  let S := TensorOrbitSetoid.tensorOrbitSetoid A P N a Γ hΓ
  have hp : ∀ p q, S.r p q → R.r p.1 q.1 := by
    rintro p q ⟨g, hg, hbase, _⟩
    exact (hR p.1 q.1).mpr ⟨g, hg, hbase⟩
  refine ⟨S, fun _ _ => Iff.rfl, QuotientSection.quotientProjection R S hp,
    QuotientSection.quotientProjection_continuous R S hp, fun _ => rfl, ?_⟩
  intro f hf
  let T := DataTheta.SymmetricGeometricTensor.symmetricGeometricTensor (GeometricGaussians.constructedComparison A P) hΘ f a
  have ht : ∀ z w, R.r z w → S.r (z, T z) (w, T w) := by
    intro z w hzw
    obtain ⟨g, hg, hbase⟩ := (hR z w).mp hzw
    refine ⟨g, hg, hbase, ?_⟩
    intro v
    have hc := (hHecke g f).2.2.2 a z v
    rw [hfix f hf g hg, hbase] at hc
    exact hc
  refine ⟨T, fun _ => rfl, QuotientSection.descendedSection R S T ht, ?_, ?_, fun _ => rfl⟩
  · exact QuotientSection.descendedSection_continuous R S T ht
      (DataTheta.SymmetricGeometricTensor.symmetricGeometricTensor_continuous (GeometricGaussians.constructedComparison A P) hΘ f a)
  · exact QuotientSection.quotientProjection_descendedSection R S hp T ht

end

end OAI.RepresentationTheory.Theta.Adelic.TensorSectionDescent
