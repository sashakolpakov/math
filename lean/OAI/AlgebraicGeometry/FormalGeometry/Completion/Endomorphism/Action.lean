import OAI.AlgebraicGeometry.FormalGeometry.Completion.CohomologyFunctoriality
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms

/-! # Action -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.Action.Construction

noncomputable section

/-!
# Completion: the opposite endomorphism monoid acts on genuine geometric H¹

The multiplication law is proved from scheme base change and cohomological
pullback. Additivity with respect to the group-scheme law, and hence extension
to the rational endomorphism algebra, is not asserted in this module.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]

theorem geometricFiberMap_id (A : Over (Spec (CommRingCat.of k))) :
    Geometric.Frobenius.Construction.geometricFiberMap k (𝟙 A) = 𝟙 (Cohomology.Construction.geometricFiber A) := by
  unfold Geometric.Frobenius.Construction.geometricFiberMap
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Pullback on geometric H¹ induced by an actual morphism over k. -/
def geometricH1Pullback {A B : Over (Spec (CommRingCat.of k))} (f : A ⟶ B) :
    Cohomology.Construction.GeometricH1 ℓ B →ₗ[AlgebraicClosure ℚ_[ℓ]] Cohomology.Construction.GeometricH1 ℓ A :=
  CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ (Geometric.Frobenius.Construction.geometricFiberMap k f)

theorem geometricH1Pullback_id (A : Over (Spec (CommRingCat.of k))) :
    geometricH1Pullback ℓ k (𝟙 A) = LinearMap.id := by
  unfold geometricH1Pullback
  rw [geometricFiberMap_id, CohomologyFunctoriality.Construction.algebraicEllAdicH1Pullback_id]

theorem geometricH1Pullback_comp {A B C : Over (Spec (CommRingCat.of k))}
    (f : A ⟶ B) (g : B ⟶ C) :
    geometricH1Pullback ℓ k (f ≫ g) =
      (geometricH1Pullback ℓ k f).comp (geometricH1Pullback ℓ k g) := by
  unfold geometricH1Pullback
  rw [Geometric.Frobenius.Construction.geometricFiberMap_comp, CohomologyFunctoriality.Construction.algebraicEllAdicH1Pullback_comp]

variable (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A]

/-- The proved multiplicative action has domain the opposite endomorphism monoid. -/
def algebraicEndOppH1MonoidHom :
    (Endomorphisms.Construction.AlgebraicEnd A)ᵐᵒᵖ →* Module.End (AlgebraicClosure ℚ_[ℓ]) (Cohomology.Construction.GeometricH1 ℓ A) where
  toFun f := geometricH1Pullback ℓ k f.unop.toMul.hom.hom
  map_one' := geometricH1Pullback_id ℓ k A
  map_mul' f g := by
    change geometricH1Pullback ℓ k (g.unop * f.unop).toMul.hom.hom = _
    rw [Endomorphisms.Construction.algebraicEnd_mul_apply, geometricH1Pullback_comp]
    rfl

variable [Fintype k]

/-- The opposite algebraic Frobenius acts as the already constructed geometric operator. -/
theorem algebraicEndOppH1MonoidHom_frobenius :
    algebraicEndOppH1MonoidHom ℓ k A (MulOpposite.op (Endomorphisms.Construction.algebraicFrobenius k A)) =
      CohomologyPullback.Construction.geometricH1Frobenius ℓ k A := rfl

/-- The geometric Frobenius operator commutes with all these endomorphism actions. -/
theorem geometricH1Frobenius_commutes (f : (Endomorphisms.Construction.AlgebraicEnd A)ᵐᵒᵖ) :
    Commute (CohomologyPullback.Construction.geometricH1Frobenius ℓ k A) (algebraicEndOppH1MonoidHom ℓ k A f) := by
  exact ((Endomorphisms.Construction.algebraicFrobenius_commutes k A f.unop).op).map
    (algebraicEndOppH1MonoidHom ℓ k A)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.Action.Construction
