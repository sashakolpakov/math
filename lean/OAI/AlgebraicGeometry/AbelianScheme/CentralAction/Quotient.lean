import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Descent
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Quotient -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Quotient.Construction

noncomputable section

/-! Equal kernels of actual isogenies give a canonical group-scheme
isomorphism. Its integral action and complete marking are preserved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies

section OverDescent

variable {C : Type*} [Category* C] {S : C} {X Y : Over S}

theorem effectiveEpiOver_of_left (f : X ⟶ Y) [EffectiveEpi f.left] : EffectiveEpi f := by
  have hraw {W : Over S} (e : X ⟶ W)
      (he : ∀ {Z : Over S} (a b : Z ⟶ X), a ≫ f = b ≫ f → a ≫ e = b ≫ e) :
      ∀ {Z : C} (a b : Z ⟶ X.left), a ≫ f.left = b ≫ f.left → a ≫ e.left = b ≫ e.left := by
    intro Z a b hab
    let Z' : Over S := Over.mk (a ≫ X.hom)
    let a' : Z' ⟶ X := Over.homMk a rfl
    let b' : Z' ⟶ X := Over.homMk b (by
      change b ≫ X.hom = a ≫ X.hom
      rw [← f.w, ← Category.assoc, ← Category.assoc, hab])
    exact congrArg Over.Hom.left (he a' b' (Over.OverMorphism.ext hab))
  let desc {W : Over S} (e : X ⟶ W)
      (he : ∀ {Z : Over S} (a b : Z ⟶ X), a ≫ f = b ≫ f → a ≫ e = b ≫ e) : Y ⟶ W :=
    Over.homMk (EffectiveEpi.desc f.left e.left (hraw e he)) (by
      apply (cancel_epi f.left).mp
      rw [← Category.assoc, EffectiveEpi.fac, e.w, f.w])
  refine ⟨⟨{ desc := desc, fac := ?_, uniq := ?_ }⟩⟩
  · intro W e he
    exact Over.OverMorphism.ext (EffectiveEpi.fac f.left e.left (hraw e he))
  · intro W e he m hm
    exact Over.OverMorphism.ext (EffectiveEpi.uniq f.left e.left (hraw e he) m.left
      (congrArg Over.Hom.left hm))

end OverDescent

section GroupFactorization

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
  {X Y Z : C} [GrpObj X] [GrpObj Y] [GrpObj Z]

theorem isMonHom_of_factorization (f : X ⟶ Y) [IsMonHom f]
    (g : X ⟶ Z) [IsMonHom g] (e : Y ⟶ Z)
    [Epi (f ⊗ₘ f)] (he : f ≫ e = g) : IsMonHom e where
  one_hom := by
    rw [← IsMonHom.one_hom f, Category.assoc, he, IsMonHom.one_hom]
  mul_hom := by
    apply (cancel_epi (f ⊗ₘ f)).mp
    rw [← Category.assoc, ← IsMonHom.mul_hom f, Category.assoc, he,
      IsMonHom.mul_hom g, ← Category.assoc, tensorHom_comp_tensorHom, he]

end GroupFactorization

variable {S : Scheme} {g : ℕ}

theorem isogeny_effectiveEpi {B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (f : B.Isogeny C) : EffectiveEpi f.hom := effectiveEpiOver_of_left f.hom

theorem isogeny_tensor_epi {B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (f : B.Isogeny C) : Epi (f.hom ⊗ₘ f.hom) := by
  have : IsFinite (f.hom ⊗ₘ f.hom).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @IsFinite) f.finite f.finite f.hom.w.symm f.hom.w.symm
  have : Flat (f.hom ⊗ₘ f.hom).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @Flat) f.flat f.flat f.hom.w.symm f.hom.w.symm
  have : Surjective (f.hom ⊗ₘ f.hom).left := by
    let : MorphismProperty.IsStableUnderComposition (@Surjective) := {
      comp_mem _ _ hf hg := ⟨hg.surj.comp hf.surj⟩ }
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @Surjective) f.surjective f.surjective f.hom.w.symm f.hom.w.symm
  have := effectiveEpiOver_of_left (f.hom ⊗ₘ f.hom)
  infer_instance

def isogenyKernelIso {B C D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (f : B.Isogeny C) (e : B.Isogeny D)
    (hker : ∀ (T : Over S) (x : T ⟶ B.scheme), x ≫ f.hom = 1 ↔ x ≫ e.hom = 1) :
    C.scheme ≅ D.scheme := by
  have := isogeny_effectiveEpi f
  have := isogeny_effectiveEpi e
  exact Descent.Construction.equalKernelQuotientIso f.hom e.hom hker

theorem isogenyKernelIso_fac {B C D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (f : B.Isogeny C) (e : B.Isogeny D)
    (hker : ∀ (T : Over S) (x : T ⟶ B.scheme), x ≫ f.hom = 1 ↔ x ≫ e.hom = 1) :
    f.hom ≫ (isogenyKernelIso f e hker).hom = e.hom := by
  have := isogeny_effectiveEpi f
  have := isogeny_effectiveEpi e
  exact Descent.Construction.equalKernelQuotientIso_fac f.hom e.hom hker

theorem isogenyKernelIso_preservesGroup {B C D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (f : B.Isogeny C) (e : B.Isogeny D)
    (hker : ∀ (T : Over S) (x : T ⟶ B.scheme), x ≫ f.hom = 1 ↔ x ≫ e.hom = 1) :
    IsMonHom (isogenyKernelIso f e hker).hom := by
  have := isogeny_tensor_epi f
  exact isMonHom_of_factorization f.hom e.hom _ (isogenyKernelIso_fac f e hker)

variable {R : Type} [CommRing R] {N n m : ℕ}

theorem isogenyKernelIso_equivariant {B C D : TateComparison.PEL.PELFamilyData R g N S}
    (f : TateComparison.PELIsogenies.PELIsogeny B C n) (e : TateComparison.PELIsogenies.PELIsogeny B D m)
    (hker : ∀ (T : Over S) (x : T ⟶ B.abelian.scheme),
      x ≫ f.isogeny.hom = 1 ↔ x ≫ e.isogeny.hom = 1) (r : R) :
    TateComparison.End.endSchemeMap C.abelian.scheme (C.action r) ≫ (isogenyKernelIso f.isogeny e.isogeny hker).hom =
      (isogenyKernelIso f.isogeny e.isogeny hker).hom ≫ TateComparison.End.endSchemeMap D.abelian.scheme (D.action r) := by
  have := isogeny_effectiveEpi f.isogeny
  apply (cancel_epi f.isogeny.hom).mp
  rw [← Category.assoc, ← f.equivariant, Category.assoc, isogenyKernelIso_fac,
    e.equivariant, ← Category.assoc, isogenyKernelIso_fac]

theorem isogenyKernelIso_marking {B C D : TateComparison.PEL.PELFamilyData R g N S}
    (f : TateComparison.PELIsogenies.PELIsogeny B C n) (e : TateComparison.PELIsogenies.PELIsogeny B D m)
    (hker : ∀ (T : Over S) (x : T ⟶ B.abelian.scheme),
      x ≫ f.isogeny.hom = 1 ↔ x ≫ e.isogeny.hom = 1)
    (T : Over S) (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    (C.marking.hom.app (.op T) c).val ≫ (isogenyKernelIso f.isogeny e.isogeny hker).hom =
      (D.marking.hom.app (.op T) c).val := by
  rw [← f.marking T c, Category.assoc, isogenyKernelIso_fac, e.marking]

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Quotient.Construction
