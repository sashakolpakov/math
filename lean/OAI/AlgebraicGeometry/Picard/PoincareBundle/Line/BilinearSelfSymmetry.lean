import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LineEndomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearFlip

/-! # Bilinear Self Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.BilinearSelfSymmetry

noncomputable section

/-! Every bilinear operation with two copies of the same line bundle is symmetric. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LineEndomorphisms

theorem linear_symmetric {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] R) (β : M →ₗ[R] M →ₗ[R] N) (a b : M) :
    β a b = β b a := by
  have hrep (m : M) : m = e m • e.symm 1 := by
    apply e.injective
    rw [e.map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]
  have hβ (m n : M) : β m n = (e m * e n) • β (e.symm 1) (e.symm 1) := by
    calc
      β m n = β (e m • e.symm 1) (e n • e.symm 1) := congrArg₂ (fun a b => β a b) (hrep m) (hrep n)
      _ = _ := by simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm]
  exact (hβ a b).trans ((congrArg (fun r => r • β (e.symm 1) (e.symm 1)) (mul_comm (e a) (e b))).trans
    (hβ b a).symm)

/-- Local rank-one frames prove symmetry on all opens of every scheme. -/
theorem app_symmetric {X : Scheme.{u}} {M P : X.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M)
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M M P) (W : X.Opens) (m n : Γ(M, W)) : β.app W m n = β.app W n m := by
  choose U hx he using hM
  let e (x : X) := Isogenies.NeighborCounting.LineEndomorphisms.overTrivialization (U x) (Classical.choice (he x))
  let PS : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨P.presheaf, P.isSheaf⟩
  have hW : W ≤ iSup (fun x => W ⊓ U x) := by
    intro x hxW
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW, hx x⟩
  apply PS.eq_of_locally_eq' (fun x => W ⊓ U x) W (fun _ => homOfLE inf_le_left) hW
  intro x
  let V : Over (U x) := Over.mk (homOfLE (show W ⊓ U x ≤ U x from inf_le_right))
  let F := SheafOfModules.forget (X.ringCatSheaf.over (U x)) ⋙ PresheafOfModules.evaluation _ (op V)
  let eV := F.mapIso (e x)
  let ev : Γ(M, W ⊓ U x) ≃ₗ[Γ(X, W ⊓ U x)] Γ(X, W ⊓ U x) := eV.toLinearEquiv
  let j : W ⊓ U x ⟶ W := homOfLE inf_le_left
  change P.presheaf.map j.op (β.app W m n) = P.presheaf.map j.op (β.app W n m)
  rw [β.naturality, β.naturality]
  exact linear_symmetric ev (β.app (W ⊓ U x)) (M.presheaf.map j.op m) (M.presheaf.map j.op n)

theorem flip_eq {X : Scheme.{u}} {M P : X.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M)
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M M P) : AbelianScheme.IsogenyQuotient.BilinearFlip.Construction.flipLineBilinear β = β := by
  ext U m n
  exact app_symmetric hM β U n m

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.BilinearSelfSymmetry
