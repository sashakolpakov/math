import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.LocalBlocks

/-! # Local Product Blocks -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalProductBlocks.CM

noncomputable section

/-! The local coordinates of the full source product recover its
active component. A supported source element has just one nontrivial
block among distinct real-subfield places. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

theorem transport_evaluation {I : Type*} {G : I → Type*} [∀ i, Group (G i)]
    (K : ∀ i, Subgroup (G i)) (v : I) {A : Type*} [Group A] (e : G v ≃* A)
    (a : A) (b : RestrictedPlaceProduct.CM.away K v) :
    e (RestrictedPlaceProduct.CM.transport K v e (a, b) v) = a :=
  (congrArg e (congrArg Prod.fst (RestrictedPlaceProduct.CM.split_assemble K v (e.symm a) b))).trans
    (e.apply_symm_apply a)

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

theorem local_product (a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q])
    (b : SourceFinite.Product.CM.Away E Q f) :
    SourceFinite.LocalBlocks.CM.localHom E Q f (SourceFinite.Product.CM.equivalence E Q f (a, b)) = a :=
  transport_evaluation (SourceFinite.Product.CM.levels E Q) (QadicPlace.CM.place E f)
    (QadicSpecialLinear.CM.equivalence E Q f) a b

variable {d : Gal(E/ℚ) → Bool} (L : GeometricSource.CM.LinePeriod E B places d)

theorem assemble (a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q])
    (w : FactorTheta.CM.RationalWeilFactorization.Away E L f) :
    SourceFinite.LocalBlocks.CM.localHom E (OppositeCoordinates.CM.coordinates E L.coordinates) f
      (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (a, w)) = a :=
  local_product E (OppositeCoordinates.CM.coordinates E L.coordinates) f a
    (RationalAwayTopology.CM.nativeCoordinates E L f w)

variable {I : Type*} [DecidableEq I] (τ : I → E →+* ℚ_[q]) (μ : I)

theorem active_blocks
    (hτ : ∀ i, i ≠ μ → QadicPlace.CM.place E (τ i) ≠ QadicPlace.CM.place E (τ μ))
    (a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    SourceFinite.LocalBlocks.CM.blocks E (τ μ) L τ (a, 1) = Pi.mulSingle μ a := by
  funext i
  by_cases hi : i = μ
  · subst i
    exact (assemble E (τ μ) L a 1).trans (by simp)
  · have hx : IntrinsicActiveClosure.CM.Intrinsic.assemble E L (τ μ) (a, 1) =
        ActiveFiniteMatrix.CM.active E (OppositeCoordinates.CM.coordinates E L.coordinates) (τ μ) a :=
      IntrinsicActiveClosure.CM.Intrinsic.active E L (τ μ) a
    exact (congrArg (SourceFinite.LocalBlocks.CM.localHom E
      (OppositeCoordinates.CM.coordinates E L.coordinates) (τ i)) hx).trans
        ((SourceFinite.LocalBlocks.CM.inactive E (OppositeCoordinates.CM.coordinates E L.coordinates)
          (τ μ) a (τ i) (hτ i hi)).trans (by simp only [Pi.mulSingle_eq_of_ne hi]))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalProductBlocks.CM
