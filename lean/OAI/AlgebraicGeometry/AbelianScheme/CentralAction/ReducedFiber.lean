import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ReducedFiberAlgebra
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Reduced Fiber -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ReducedFiber.Construction

noncomputable section

/-! Detect reduced finite fibers using their geometric point count and
their finite-flat rank. The affine presentation is constructed from the scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u
variable (k : Type u) [Field k]

def algSpecBaseIso : Over.mk (𝟙 (Spec (.of k))) ≅
    (algSpec (.of k)).obj (op (CommAlgCat.of k k)) :=
  Over.isoMk (Iso.refl _) (by simp [algSpec_obj_hom]; exact Category.id_comp _)

def algSpecPointEquiv (A : CommAlgCat.{u} k) :
    (Over.mk (𝟙 (Spec (.of k))) ⟶ (algSpec (.of k)).obj (op A)) ≃ (A →ₐ[k] k) := by
  let e₁ := Iso.homCongr (algSpecBaseIso k) (Iso.refl ((algSpec (.of k)).obj (op A)))
  let e₂ := (algSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv
    (X := op (CommAlgCat.of k k)) (Y := op A)
  refine e₁.trans (e₂.symm.trans ?_)
  exact {
    toFun := fun f => f.unop.hom
    invFun := fun f => (CommAlgCat.ofHom f).op
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- A finite flat scheme over a field is etale if its rational points
account for its entire rank. Thus the argument detects nilpotent structure. -/
theorem finite_field_scheme_etale_of_point_count
    (Y : Over (Spec (.of k))) [IsFinite Y.hom] [Flat Y.hom]
    (hcard : Nat.card (Over.mk (𝟙 (Spec (.of k))) ⟶ Y) =
      Y.hom.finrank (default : Spec (.of k))) : Etale Y.hom := by
  have hAffine : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k) (G := Y)).mpr hAffine
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  have hf : IsFinite ((algSpec (.of k)).obj A).hom := by
    rw [← e.hom.w]
    infer_instance
  have : Module.Finite k A.unop := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k A.unop))) at hf
    exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hf)
  have hdim : Y.hom.finrank (default : Spec (.of k)) = Module.finrank k A.unop := by
    rw [← Scheme.Hom.finrank_comp_left_of_isIso e.hom.left Y.hom, e.hom.w]
    change (Spec.map (CommRingCat.ofHom (algebraMap k A.unop))).finrank default = _
    exact (Scheme.Hom.finrank_SpecMap_algebraMap k A.unop (default : Spec (.of k))).trans
      (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := k) (M := A.unop))
        (default : Spec (.of k)))
  have hcount : Nat.card (A.unop →ₐ[k] k) = Module.finrank k A.unop := by
    rw [← Nat.card_congr (algSpecPointEquiv k A.unop)]
    exact (Nat.card_congr (Iso.homCongr (Iso.refl _) e)).trans (hcard.trans hdim)
  have : Algebra.Etale k A.unop := ReducedFiberAlgebra.Construction.finite_algebra_etale_of_point_count k A.unop hcount
  have : Etale ((algSpec (.of k)).obj A).hom := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap k A.unop)))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  rw [← e.inv.w]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ReducedFiber.Construction
