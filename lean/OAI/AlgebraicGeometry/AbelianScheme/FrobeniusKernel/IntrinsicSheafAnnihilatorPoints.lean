import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.Pairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.AnnihilatorSections

/-! # Intrinsic Sheaf Annihilator Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicSheafAnnihilatorPoints.Construction

noncomputable section

/-! Translate exact native sheaf annihilators into point conditions on
all test schemes, keeping the specified native subgroup inclusions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {G K H : Grp (Over S)}
  [IsCommMonObj G.X] [IsCommMonObj K.X] [IsCommMonObj H.X]
  (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S K))
  (i : H ⟶ G) [Mono i.hom.hom]

theorem nativeSheafAnnihilator_membership (T : Over S) (y : T ⟶ K.X) :
    ULift.up y ∈ IsogenyQuotient.Sheaf.KernelSections.Construction.sheafSubobjectSections T (CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e (IsogenyQuotient.Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i)) ↔
      ∀ (U : Over S) (t : U ⟶ T) (x : U ⟶ H.X),
        CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) U
          (e.rightAdjoint.hom.app (.op U) (ULift.up (t ≫ y)))
          (ULift.up (x ≫ i.hom.hom)) = 1 := by
  have h := (IsogenyQuotient.Sheaf.Pairing.Construction.sheafPairingToScheme e).toSheafPairing_annihilator_sections i T y
  rw [IsogenyQuotient.Sheaf.Pairing.Construction.sheafPairingToScheme_toSheaf] at h
  refine h.trans ?_
  apply forall_congr'
  intro U
  apply forall_congr'
  intro t
  apply forall_congr'
  intro x
  have hv := (IsogenyQuotient.Sheaf.Pairing.Construction.sheafPairingToScheme_value e U (x ≫ i.hom.hom) (t ≫ y)).trans
    (IsogenyQuotient.Sheaf.Pairing.Construction.sheafPairingNativeValue_right e U (x ≫ i.hom.hom) (t ≫ y))
  exact ⟨fun hz => ULift.ext _ _ (hv.symm.trans hz),
    fun hz => hv.trans (congrArg ULift.down hz)⟩

theorem sheafPairing_flip_rightValue (T : Over S)
    (x : (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G).obj.obj (.op T))
    (y : (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S K).obj.obj (.op T)) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S K) T (e.flip.rightAdjoint.hom.app (.op T) x) y =
      CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) T (e.rightAdjoint.hom.app (.op T) y) x :=
  (congrArg (fun f => CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S K) T (f.hom.app (.op T) x) y)
    (congrArg CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.leftAdjoint e.flip_flip)).trans (e.adjoint_value T x y).symm

variable {J : Grp (Over S)} [IsCommMonObj J.X]
  (j : J ⟶ K) [Mono j.hom.hom]

/-- The native second annihilator gives the exact original subgroup,
with every restriction of the parameter point retained. -/
theorem nativeSheafDoubleAnnihilator_membership
    (hd : CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e.flip (IsogenyQuotient.Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf j) = IsogenyQuotient.Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i)
    (T : Over S) (x : T ⟶ G.X) :
    (∀ (U : Over S) (t : U ⟶ T) (y : U ⟶ J.X),
      CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) U
        (e.rightAdjoint.hom.app (.op U) (ULift.up (y ≫ j.hom.hom)))
        (ULift.up (t ≫ x)) = 1) ↔
      ∃ z : T ⟶ H.X, z ≫ i.hom.hom = x := by
  have hm := nativeSheafAnnihilator_membership e.flip j T x
  have hh := congrArg (fun F : Subobject (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) =>
    ULift.up x ∈ IsogenyQuotient.Sheaf.KernelSections.Construction.sheafSubobjectSections T F) hd
  refine Iff.trans ?_ (hm.symm.trans ((iff_of_eq hh).trans (IsogenyQuotient.Sheaf.AnnihilatorSections.Construction.mem_nativeSubgroupSheaf_sections i T x)))
  apply forall_congr'
  intro U
  apply forall_congr'
  intro t
  apply forall_congr'
  intro y
  exact iff_of_eq (congrArg (fun z => z = 1)
    (sheafPairing_flip_rightValue e U (ULift.up (t ≫ x)) (ULift.up (y ≫ j.hom.hom)))).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicSheafAnnihilatorPoints.Construction
