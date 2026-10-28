import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Translations
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Global Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.GlobalFunctions

noncomputable section

/-! Global regular functions on a constant scheme are exactly label-indexed functions with values in the base ring of global functions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable (S : Scheme.{u}) (I : Type u)

def constantSchemeGlobalRingIso :
    Γ((Iff.constantScheme S I).left, ⊤) ≅ CommRingCat.of (I → Γ(S, ⊤)) :=
  Scheme.Γ.mapIso (opCoproductIsoProduct (fun _ : I => S)) ≪≫
    PreservesProduct.iso Scheme.Γ (fun _ : I => Opposite.op S) ≪≫
      CommRingCat.piIsoPi (fun _ : I => Γ(S, ⊤))

theorem constantSchemeGlobalRingIso_projection (i : I) :
    (constantSchemeGlobalRingIso S I).hom ≫ CommRingCat.ofHom (Pi.evalRingHom (fun _ : I => Γ(S, ⊤)) i) =
      (Sigma.ι (fun _ : I => S) i).appTop := by
  have hp : (CommRingCat.piIsoPi (fun _ : I => Γ(S, ⊤))).hom ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun _ : I => Γ(S, ⊤)) i) =
        Pi.π (fun _ : I => Γ(S, ⊤)) i :=
    limit.isoLimitCone_hom_π ⟨_, CommRingCat.piFanIsLimit (fun _ : I => Γ(S, ⊤))⟩ ⟨i⟩
  have h₂ : ((PreservesProduct.iso Scheme.Γ (fun _ : I => Opposite.op S)).hom ≫
      (CommRingCat.piIsoPi (fun _ : I => Γ(S, ⊤))).hom) ≫
        CommRingCat.ofHom (Pi.evalRingHom (fun _ : I => Γ(S, ⊤)) i) =
          Scheme.Γ.map (Pi.π (fun _ : I => Opposite.op S) i) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => (PreservesProduct.iso Scheme.Γ (fun _ : I => Opposite.op S)).hom ≫ k) hp).trans
        (piComparison_comp_π Scheme.Γ (fun _ : I => Opposite.op S) i))
  have h₁ : Scheme.Γ.map (opCoproductIsoProduct (fun _ : I => S)).hom ≫
      Scheme.Γ.map (Pi.π (fun _ : I => Opposite.op S) i) =
        (Sigma.ι (fun _ : I => S) i).appTop :=
    (Scheme.Γ.map_comp _ _).symm.trans
      (congrArg Scheme.Γ.map (opCoproductIsoProduct_hom_comp_π (Z := fun _ : I => S) i))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => Scheme.Γ.map (opCoproductIsoProduct (fun _ : I => S)).hom ≫ k) h₂).trans h₁)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.GlobalFunctions
