import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.KernelScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.EffectiveDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidHomEpiDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfullyFlatTensorEpi
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Kernel Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Group homomorphisms annihilating the actual kernel descend uniquely through a finite-flat isogeny. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {g h k : ℕ}
variable {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S} (p : Abelian.Schemes.AbelianScheme.Isogeny A B) (C : Abelian.Schemes.AbelianScheme k S)

theorem Abelian.Schemes.AbelianScheme.Isogeny.kernel_annihilator_relation (m : A.scheme ⟶ C.scheme) [IsMonHom m]
    (hm : p.kernelInclusion ≫ m = 1) {T : Over S} (a b : T ⟶ A.scheme)
    (hab : a ≫ p.hom = b ≫ p.hom) : a ≫ m = b ≫ m := by
  let t : p.kernelAt T := ⟨b / a, by
    change (b / a) ≫ p.hom = 1
    rw [GrpObj.div_comp, div_eq_one]
    exact hab.symm⟩
  let e := (p.kernelSchemePointsEquiv T).symm t
  have he : e ≫ p.kernelInclusion = b / a :=
    congrArg (fun x : p.kernelAt T => x.val) ((p.kernelSchemePointsEquiv T).apply_symm_apply t)
  have hz : (b / a) ≫ m = 1 := by
    calc
      _ = (e ≫ p.kernelInclusion) ≫ m := congrArg (fun f => f ≫ m) he.symm
      _ = e ≫ (1 : p.kernelScheme ⟶ C.scheme) :=
        (Category.assoc _ _ _).trans (congrArg (fun f => e ≫ f) hm)
      _ = 1 := MonObj.comp_one e
  exact (div_eq_one.mp ((GrpObj.div_comp b a m).symm.trans hz)).symm

theorem Abelian.Schemes.AbelianScheme.Isogeny.existsUnique_kernel_factor (m : A.scheme ⟶ C.scheme) [IsMonHom m]
    (hm : p.kernelInclusion ≫ m = 1) : ∃! d : B.scheme ⟶ C.scheme, p.hom ≫ d = m := by
  have : EffectiveEpi p.hom.left := inferInstance
  exact HilbertConstruction.Over.EffectiveDescent.over_existsUnique_factor_of_effectiveEpi p.hom m
    (fun a b hab => p.kernel_annihilator_relation C m hm a b hab)

theorem Abelian.Schemes.AbelianScheme.Isogeny.kernel_factor_isMonHom (m : A.scheme ⟶ C.scheme) (d : B.scheme ⟶ C.scheme)
    [IsMonHom m] (hd : p.hom ≫ d = m) : IsMonHom d := by
  have : Epi (p.hom ⊗ₘ p.hom) := FaithfullyFlatTensorEpi.over_tensor_epi_of_flat_surjective p.hom p.hom
  exact MonoidHomEpiDescent.isMonHom_of_tensor_epi p.hom m d hd

theorem Abelian.Schemes.AbelianScheme.Isogeny.existsUnique_group_kernel_factor (m : A.scheme ⟶ C.scheme) [IsMonHom m]
    (hm : p.kernelInclusion ≫ m = 1) :
    ∃! d : {f : B.scheme ⟶ C.scheme // IsMonHom f}, p.hom ≫ d.val = m := by
  obtain ⟨d, hd, huniq⟩ := p.existsUnique_kernel_factor C m hm
  refine ⟨⟨d, p.kernel_factor_isMonHom C m d hd⟩, hd, ?_⟩
  intro e he
  exact Subtype.ext (huniq e.val he)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
