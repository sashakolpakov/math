import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.AnnihilatorPoints
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.SelfAnnihilatorType
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PairingNondegeneracy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeUnitEquiv
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateFiniteness

/-! # Pairing Characters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PairingCharacters

noncomputable section

/-! The original scheme pairing gives an actual finite character
pairing on geometric points. Full relative self-annihilation therefore
preserves the subgroup's finite abstract group type in its quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

def geometricMultiplicativePointEquiv (k : Type) [Field k] :
    (Over.mk (𝟙 (Spec (.of k))) ⟶ (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) ≃* kˣ :=
  (AbelianScheme.IsogenyQuotient.MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv (Over.mk (𝟙 (Spec (.of k))))).trans
    (Units.mapEquiv (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv)

variable {k : Type} [Field k]
    {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
    (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := A) (B := A) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))

def geometricPairingCharacters :
    (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →*
      ((Over.mk (𝟙 (Spec (.of k))) ⟶ A) →* kˣ) where
  toFun x := (geometricMultiplicativePointEquiv k).toMonoidHom.comp (e.pairLeftHom x)
  map_one' := by
    apply MonoidHom.ext
    intro y
    change geometricMultiplicativePointEquiv k (e.pairValue y 1) = 1
    have h : e.pairValue y 1 = 1 := e.one_right _ y
    rw [h, map_one]
  map_mul' x z := by
    apply MonoidHom.ext
    intro y
    change geometricMultiplicativePointEquiv k (e.pairValue y (x * z)) =
      geometricMultiplicativePointEquiv k (e.pairValue y x) *
        geometricMultiplicativePointEquiv k (e.pairValue y z)
    have h : e.pairValue y (x * z) = e.pairValue y x * e.pairValue y z := e.mul_right _ y x z
    rw [h, map_mul]

theorem geometricPairingCharacters_eq_one_iff
    (x y : Over.mk (𝟙 (Spec (.of k))) ⟶ A) :
    geometricPairingCharacters e x y = 1 ↔ e.pairValue y x = 1 :=
  map_eq_one_iff (geometricMultiplicativePointEquiv k) (geometricMultiplicativePointEquiv k).injective

variable [IsAlgClosed k] [IsFinite A.hom] [Etale A.hom]

omit [IsFinite A.hom] in
theorem geometricPairingCharacters_nondegenerate (he : e.toSheafPairing.IsPerfect)
    (x : Over.mk (𝟙 (Spec (.of k))) ⟶ A)
    (hx : ∀ y, geometricPairingCharacters e x y = 1) : x = 1 := by
  let : IsReduced A.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field A.hom
  have hf : e.flip.toSheafPairing.IsPerfect := by
    rw [e.toSheafPairing_flip]
    refine ⟨he.2, ?_⟩
    have h : e.toSheafPairing.flip.rightAdjoint = e.toSheafPairing.leftAdjoint :=
      congrArg AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.leftAdjoint (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.flip_flip e.toSheafPairing)
    exact h.symm ▸ he.1
  apply AbelianScheme.TateComparison.PairingNondegeneracy.schemePairing_geometric_nondegenerate_left e.flip hf x
  intro y
  rw [e.flip_pairValue]
  exact (geometricPairingCharacters_eq_one_iff e x y).mp (hx y)

theorem geometric_self_annihilator_quotient_type [CharZero k]
    (he : e.toSheafPairing.IsPerfect)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A (Over.mk (𝟙 (Spec (.of k))))) (R : F.Model)
    (hF : e.relativeAnnihilator F = F) :
    Nonempty (((Over.mk (𝟙 (Spec (.of k))) ⟶ A) ⧸
      F.points (Over.mk (𝟙 (Spec (.of k)))) (𝟙 _)) ≃*
        F.points (Over.mk (𝟙 (Spec (.of k)))) (𝟙 _)) := by
  let T : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))
  let : Finite (T ⟶ A) := AbelianScheme.IsogenyQuotient.Geometric.TateFiniteness.Construction.finite_over_geometric_points A k (𝟙 (Spec (.of k)))
  apply ReferenceFamily.Finite.SelfAnnihilatorType.finite_self_annihilator_quotient_type (geometricPairingCharacters e)
    (geometricPairingCharacters_nondegenerate e he)
  intro x
  constructor
  · intro hx
    have hm : x ∈ (e.relativeAnnihilator F).points T (𝟙 T) := by
      apply (AnnihilatorPoints.geometric_annihilator_membership e F R x).mpr
      intro y hy
      exact (geometricPairingCharacters_eq_one_iff e x y).mp (hx y hy)
    rwa [hF] at hm
  · intro hx y hy
    have hm : x ∈ (e.relativeAnnihilator F).points T (𝟙 T) := hF.symm ▸ hx
    exact (geometricPairingCharacters_eq_one_iff e x y).mpr
      ((AnnihilatorPoints.geometric_annihilator_membership e F R x).mp hm y hy)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PairingCharacters
