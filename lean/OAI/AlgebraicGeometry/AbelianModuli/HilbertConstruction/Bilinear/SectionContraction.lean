import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves

/-! # Section Contraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear

noncomputable section

/-! Contracting a natural bilinear pairing with an actual global section gives a morphism of module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M N P Q : X.Modules} (β : Sheaves.SheafBilinearMap M N P)

def Sheaves.SheafBilinearMap.contractLeft (s : Γ(M, ⊤)) : N ⟶ P where
  val := {
    app V := ModuleCat.ofHom (β.app V.unop (M.presheaf.map V.unop.leTop.op s))
    naturality {V W} h := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hr : M.presheaf.map h (M.presheaf.map V.unop.leTop.op s) =
          M.presheaf.map W.unop.leTop.op s := by
        rw [← M.presheaf.map_comp_apply]
        rfl
      exact (congrArg (fun a => β.app W.unop a (N.presheaf.map h x)) hr).symm.trans
        (β.naturality h.unop (M.presheaf.map V.unop.leTop.op s) x).symm }

theorem Sheaves.SheafBilinearMap.contractLeft_app (s : Γ(M, ⊤)) (V : X.Opens) (x : Γ(N, V)) :
    (β.contractLeft s).app V x = β.app V (M.presheaf.map V.leTop.op s) x := rfl

theorem Sheaves.SheafBilinearMap.contractLeft_zero : β.contractLeft 0 = 0 := by
  apply Scheme.Modules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  intro x
  change β.app V (M.presheaf.map V.leTop.op 0) x = 0
  simp only [map_zero, LinearMap.zero_apply]

theorem Sheaves.SheafBilinearMap.contractLeft_precomp (s : Γ(M, ⊤)) (q : Q ⟶ N) :
    q ≫ β.contractLeft s = (β.precomp (𝟙 M) q).contractLeft s := by
  apply Scheme.Modules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear
