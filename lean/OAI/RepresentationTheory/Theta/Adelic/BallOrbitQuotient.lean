import OAI.RepresentationTheory.Theta.Adelic.BallProper
import OAI.RepresentationTheory.Theta.Adelic.CompactQuotientProjection
import OAI.RepresentationTheory.Theta.Adelic.TensorOrbitSetoid

/-! # Ball Orbit Quotient -/

namespace OAI.RepresentationTheory.Theta.Adelic.BallOrbitQuotient

noncomputable section

/-! Identify the exact rational ball-orbit relation, and transfer the
topology of a compact discrete matrix-group quotient to it. -/

open scoped Classical _root_.NumberField

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.BallProper
open OAI.RepresentationTheory.Theta.Adelic.TensorOrbitSetoid OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)
variable (N : ℕ) (Γ : Subgroup (SpecialUnitary.SU H.val)) (hΓ : ∀ g, g ∈ Γ ↔ BallGeometryData.PrincipalLevel N g)

def rationalImageBallSetoid : Setoid BallNatural.Ball := MulAction.orbitRel (Γ.map (TensorOrbitSetoid.rationalBallHom A)) BallNatural.Ball

include hΓ in
theorem rationalImageBallSetoid_iff (z w : BallNatural.Ball) :
    (rationalImageBallSetoid A Γ).r z w ↔ DataTheta.Descent.BallOrbit (GeometricGaussians.constructedComparison A P) N z w := by
  change (∃ g : Γ.map (TensorOrbitSetoid.rationalBallHom A), g • w = z) ↔ _
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨r, hr, he⟩ := g.property
    refine ⟨r⁻¹, (hΓ r⁻¹).mp (Γ.inv_mem hr), ?_⟩
    change TensorOrbitSetoid.rationalBallHom A r⁻¹ • z = w
    rw [map_inv, he, ← hg]
    exact inv_smul_smul g.val w
  · rintro ⟨r, hr, he⟩
    refine ⟨⟨TensorOrbitSetoid.rationalBallHom A r⁻¹, ⟨r⁻¹, Γ.inv_mem ((hΓ r).mpr hr), rfl⟩⟩, ?_⟩
    change TensorOrbitSetoid.rationalBallHom A r⁻¹ • w = z
    change TensorOrbitSetoid.rationalBallHom A r • z = w at he
    rw [map_inv, ← he]
    exact inv_smul_smul _ _

include hΓ in
theorem ballOrbitQuotient_of_compact_discrete
    [DiscreteTopology (Γ.map (TensorOrbitSetoid.rationalBallHom A))]
    [CompactSpace (BallNatural.BallGroup ⧸ Γ.map (TensorOrbitSetoid.rationalBallHom A))] :
    ∃ R : Setoid BallNatural.Ball, (∀ z w, R.r z w ↔ DataTheta.Descent.BallOrbit (GeometricGaussians.constructedComparison A P) N z w) ∧
      CompactSpace (Quotient R) ∧ T2Space (Quotient R) ∧ SecondCountableTopology (Quotient R) := by
  let Δ := Γ.map (TensorOrbitSetoid.rationalBallHom A)
  let : ProperSMul Δ BallNatural.Ball := inferInstance
  let : SecondCountableTopology BallNatural.Ball := inferInstanceAs
    (SecondCountableTopology {z : Fin 2 → ℂ | Complex.normSq (z 0) + Complex.normSq (z 1) < 1})
  refine ⟨rationalImageBallSetoid A Γ, rationalImageBallSetoid_iff A P N Γ hΓ,
    Geometry.ComplexBall.QuotientCompact.Arithmetic.compact_orbitQuotient_of_compact_cosets Δ
      ⟨0, by change Complex.normSq 0 + Complex.normSq 0 < 1; norm_num⟩,
    (show T2Space (Quotient (MulAction.orbitRel Δ BallNatural.Ball)) from inferInstance), ?_⟩
  change SecondCountableTopology (Quotient (MulAction.orbitRel Δ BallNatural.Ball))
  exact ContinuousConstSMul.secondCountableTopology

end

end OAI.RepresentationTheory.Theta.Adelic.BallOrbitQuotient
