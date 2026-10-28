import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafSummands

/-! # Summand Intertwining -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.SummandIntertwining

noncomputable section

/-! A map intertwining actual sheaf projectors induces a map between their summands, and an intertwining isomorphism induces an actual summand isomorphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} {M N : X.Modules}

def sheafSummandIntertwiningMap (p : End M) (q : End N) (φ : M ⟶ N)
    (h : p ≫ φ = φ ≫ q) : IdempotentSheafSummands.idempotentSheafSummand p ⟶ IdempotentSheafSummands.idempotentSheafSummand q :=
  equalizer.lift (IdempotentSheafSummands.idempotentSheafInclusion p ≫ φ) (by
    rw [Category.comp_id]
    exact ((Category.assoc _ _ _).trans
      ((congrArg (fun k => IdempotentSheafSummands.idempotentSheafInclusion p ≫ k) h.symm).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ φ) (IdempotentSheafSummands.idempotentSheafInclusion_fixed p))))).symm)

@[reassoc]
theorem sheafSummandIntertwiningMap_inclusion (p : End M) (q : End N) (φ : M ⟶ N)
    (h : p ≫ φ = φ ≫ q) :
    sheafSummandIntertwiningMap p q φ h ≫ IdempotentSheafSummands.idempotentSheafInclusion q = IdempotentSheafSummands.idempotentSheafInclusion p ≫ φ :=
  equalizer.lift_ι _ _

theorem sheafProjector_intertwining_inverse (p : End M) (q : End N) (e : M ≅ N)
    (h : p ≫ e.hom = e.hom ≫ q) : q ≫ e.inv = e.inv ≫ p := by
  have ht := congrArg (fun k : M ⟶ N => e.inv ≫ k ≫ e.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] using ht.symm

def sheafSummandIntertwiningIso (p : End M) (q : End N) (e : M ≅ N)
    (h : p ≫ e.hom = e.hom ≫ q) : IdempotentSheafSummands.idempotentSheafSummand p ≅ IdempotentSheafSummands.idempotentSheafSummand q where
  hom := sheafSummandIntertwiningMap p q e.hom h
  inv := sheafSummandIntertwiningMap q p e.inv (sheafProjector_intertwining_inverse p q e h)
  hom_inv_id := by
    apply (cancel_mono (IdempotentSheafSummands.idempotentSheafInclusion p)).mp
    simp only [Category.assoc, sheafSummandIntertwiningMap_inclusion,
      sheafSummandIntertwiningMap_inclusion_assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (IdempotentSheafSummands.idempotentSheafInclusion q)).mp
    simp only [Category.assoc, sheafSummandIntertwiningMap_inclusion,
      sheafSummandIntertwiningMap_inclusion_assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.SummandIntertwining
