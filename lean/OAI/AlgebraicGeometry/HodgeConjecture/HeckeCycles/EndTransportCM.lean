import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluationCM
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

/-! # End Transport CM -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndTransportCM.CM

noncomputable section

/-! Endomorphism rings are transported along actual group-scheme
isomorphisms, and extension of the ground field is faithful. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

variable {S : Scheme} {A B : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  (e : A ≅ B) [IsMonHom e.hom]

def transport : AbelianScheme.TateComparison.End.IntegralEnd A ≃+* AbelianScheme.TateComparison.End.IntegralEnd B where
  toFun f := AbelianScheme.TateComparison.End.endOfSchemeMap B (e.inv ≫ AbelianScheme.TateComparison.End.endSchemeMap A f ≫ e.hom)
  invFun f := AbelianScheme.TateComparison.End.endOfSchemeMap A (e.hom ≫ AbelianScheme.TateComparison.End.endSchemeMap B f ≫ e.inv)
  left_inv f := by
    apply AbelianScheme.TateComparison.End.endSchemeMap_injective A
    simp only [AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id]
  right_inv f := by
    apply AbelianScheme.TateComparison.End.endSchemeMap_injective B
    simp only [AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  map_add' f g := by
    apply AbelianScheme.TateComparison.End.endSchemeMap_injective B
    simp only [AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap, AbelianScheme.TateComparison.BaseChange.endSchemeMap_add, MonObj.comp_mul, MonObj.mul_comp]
  map_mul' f g := by
    apply AbelianScheme.TateComparison.End.endSchemeMap_injective B
    simp only [AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap, AbelianScheme.TateComparison.BaseChange.endSchemeMap_mul, Category.assoc,
      Iso.hom_inv_id_assoc]

theorem transport_schemeMap (f : AbelianScheme.TateComparison.End.IntegralEnd A) :
    AbelianScheme.TateComparison.End.endSchemeMap B (transport e f) = e.inv ≫ AbelianScheme.TateComparison.End.endSchemeMap A f ≫ e.hom :=
  AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap B _

theorem transport_points (T : Over S) (p : T ⟶ A) (f : AbelianScheme.TateComparison.End.IntegralEnd A) :
    ((transport e f).app (.op T)).hom (Additive.ofMul (p ≫ e.hom)) =
      Additive.ofMul (((f.app (.op T)).hom (Additive.ofMul p)).toMul ≫ e.hom) := by
  apply Additive.toMul.injective
  rw [AbelianScheme.TateComparison.End.endSchemeMap_points, transport_schemeMap, AbelianScheme.TateComparison.End.endSchemeMap_points]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

theorem endBaseChange_injective_field
    {k L : Type} [Field k] [Field L] (σ : k →+* L)
    (G : Over (Spec (.of k))) [GrpObj G] [IsCommMonObj G] :
    Function.Injective (AbelianScheme.TateComparison.BaseChange.endBaseChange G (Spec.map (CommRingCat.ofHom σ))) := by
  let b : Spec (.of L) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom σ)
  let : GrpObj (AbelianScheme.TateComparison.BaseChange.baseChangedGroup G b).X := (AbelianScheme.TateComparison.BaseChange.baseChangedGroup G b).grp
  let : IsCommMonObj (AbelianScheme.TateComparison.BaseChange.baseChangedGroup G b).X := (AbelianScheme.TateComparison.BaseChange.baseChangedGroup G b).comm
  let : Surjective b := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  let : Flat b := inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom σ)))
  let : ∀ (Z : Scheme) (g : Z ⟶ Spec (.of k)), Epi (CategoryTheory.Limits.pullback.fst g b) :=
    fun Z g => Flat.epi_of_flat_of_surjective (CategoryTheory.Limits.pullback.fst g b)
  intro f g h
  apply AbelianScheme.TateComparison.End.endSchemeMap_injective G
  apply (Over.pullback b).map_injective
  exact (AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap G b f).symm.trans
    ((congrArg (AbelianScheme.TateComparison.End.endSchemeMap (AbelianScheme.TateComparison.BaseChange.baseChangedGroup G b).X) h).trans
      (AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap G b g))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndTransportCM.CM
