import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.PushforwardFunctor

/-! # Contravariant Iso Intertwining -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ContravariantIsoIntertwining

noncomputable section

/-! A contravariant functor transports an actual equivariant isomorphism to an intertwining isomorphism. -/
open _root_.CategoryTheory
variable {C D : Type*} [Category* C] [Category* D]

theorem contravariantFunctor_iso_intertwines (F : Cᵒᵖ ⥤ D) {X Y : C}
    (e : X ≅ Y) (σ : X ⟶ X) (τ : Y ⟶ Y) (h : σ ≫ e.hom = e.hom ≫ τ) :
    F.map τ.op ≫ (F.mapIso e.op).hom = (F.mapIso e.op).hom ≫ F.map σ.op := by
  change F.map τ.op ≫ F.map e.hom.op = F.map e.hom.op ≫ F.map σ.op
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg (fun k : X ⟶ Y => F.map k.op) h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ContravariantIsoIntertwining
