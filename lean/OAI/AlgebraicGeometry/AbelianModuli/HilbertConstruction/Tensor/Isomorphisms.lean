import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles

/-! # Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Invariance of tensor powers and ampleness under isomorphism of line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

namespace Tensor

variable {L M P Q : X.Modules} {n : ℕ}

/-- Precompose every argument of a sheaf-multilinear map by a module morphism. -/
def Powers.SheafMultilinearMap.precomp (β : Powers.SheafMultilinearMap L n P) (f : M ⟶ L) : Powers.SheafMultilinearMap M n P where
  app U := (β.app U).compLinearMap (fun _ => Powers.SheafMultilinearMap.homApp f U)
  naturality {U V} h s := by
    exact (β.naturality h (fun i => f.app U (s i))).trans
      (congrArg (β.app V) (funext fun i =>
        (ConcreteCategory.congr_hom (f.mapPresheaf.naturality h.op) (s i)).symm))

@[simp]
theorem Powers.SheafMultilinearMap.precomp_id (β : Powers.SheafMultilinearMap L n P) : β.precomp (𝟙 L) = β := by
  ext U s
  rfl

theorem Powers.SheafMultilinearMap.precomp_comp (β : Powers.SheafMultilinearMap L n P) (f : M ⟶ L) (h : Q ⟶ M) :
    (β.precomp f).precomp h = β.precomp (h ≫ f) := by
  ext U s
  rfl

theorem Powers.SheafMultilinearMap.precomp_postcomp (β : Powers.SheafMultilinearMap L n P) (f : M ⟶ L) (h : P ⟶ Q) :
    (β.postcomp h).precomp f = (β.precomp f).postcomp h := by
  ext U s
  rfl

/-- An isomorphism of the input module induces an equivalence of multilinear maps. -/
def Powers.SheafMultilinearMap.sourceIso (e : L ≅ M) (n : ℕ) (P : X.Modules) :
    Powers.SheafMultilinearMap L n P ≃ Powers.SheafMultilinearMap M n P where
  toFun β := β.precomp e.inv
  invFun β := β.precomp e.hom
  left_inv β := (β.precomp_comp e.inv e.hom).trans
    ((congrArg (fun f : L ⟶ L => β.precomp f) e.hom_inv_id).trans β.precomp_id)
  right_inv β := (β.precomp_comp e.hom e.inv).trans
    ((congrArg (fun f : M ⟶ M => β.precomp f) e.inv_hom_id).trans β.precomp_id)

end Tensor

/-- Replacing a module by an isomorphic one leaves its tensor powers unchanged. -/
theorem Tensor.Powers.IsTensorPower.of_sourceIso {L M P : X.Modules} {n : ℕ}
    (hP : Tensor.Powers.IsTensorPower L n P) (e : L ≅ M) : Tensor.Powers.IsTensorPower M n P := by
  obtain ⟨β, hβ⟩ := hP
  refine ⟨β.precomp e.inv, fun Q => ?_⟩
  have h : (fun f : P ⟶ Q => (β.precomp e.inv).postcomp f) =
      fun f : P ⟶ Q => Tensor.Powers.SheafMultilinearMap.sourceIso e n Q (β.postcomp f) := by
    funext f
    exact (β.precomp_postcomp e.inv f).symm
  rw [h]
  exact (Tensor.Powers.SheafMultilinearMap.sourceIso e n Q).bijective.comp (hβ Q)

/-- Ampleness depends only on the isomorphism class of the line bundle. -/
theorem Line.Bundles.LineBundle.IsAmple.of_iso {L M : Line.Bundles.LineBundle X} (hL : L.IsAmple)
    (e : L.sheaf ≅ M.sheaf) : M.IsAmple := by
  refine ⟨hL.1, fun x => ?_⟩
  obtain ⟨n, hn, P, hP, s, hxs, hs⟩ := hL.2 x
  exact ⟨n, hn, P, hP.of_sourceIso e, s, hxs, hs⟩

/-- Equivalent module sheaves give the same ampleness condition. -/
theorem Line.Bundles.LineBundle.isAmple_iff_of_iso {L M : Line.Bundles.LineBundle X} (e : L.sheaf ≅ M.sheaf) :
    L.IsAmple ↔ M.IsAmple :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
