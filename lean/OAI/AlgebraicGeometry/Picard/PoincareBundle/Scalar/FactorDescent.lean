import OAI.AlgebraicGeometry.Picard.PoincareBundle.FaithfulFactorDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MonoidalHomReflection
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MonoidalScalarPreservation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.PullbackCancellation

/-! # Factor Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.FactorDescent

/-! Complementary maps turn a local polarization equation into effective descent through an actual scalar quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v u' v'

section Scalar

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A B P Q : C} [GrpObj B] [GrpObj P]
  (f : A ⟶ B) (g : B ⟶ A) (d : P ⟶ Q) (e : Q ⟶ P) (l : A ⟶ Q)
  (n : ℕ) (hgf : g ≫ f = (𝟙 B) ^ n) (hde : d ≫ e = (𝟙 P) ^ n)

include hgf hde

/-- The two complementary scalar identities imply a single scalar-factorization equation. -/
theorem scaled_equation (m : B ⟶ P) [IsMonHom m] (h : f ≫ m ≫ d = l) :
    ((𝟙 B) ^ (n * n)) ≫ m = g ≫ l ≫ e := by
  have hs : ((𝟙 B) ^ (n * n)) ≫ m = ((𝟙 B) ^ n) ≫ m ≫ ((𝟙 P) ^ n) := by
    rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp,
      Category.id_comp, MonObj.pow_comp, Category.id_comp, pow_mul]
  exact hs.trans
    ((congrArg₂ (fun a b => a ≫ m ≫ b) hgf.symm hde.symm).trans (by
      simpa only [Category.assoc] using congrArg (fun t => g ≫ t ≫ e) h))

end Scalar

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] [F.Faithful]
  {A B P Q : C} [GrpObj B] [GrpObj P]
  (f : A ⟶ B) [Epi f] (g : B ⟶ A) (d : P ⟶ Q) (e : Q ⟶ P) (l : A ⟶ Q)
  (n : ℕ) (hgf : g ≫ f = (𝟙 B) ^ n) (hde : d ≫ e = (𝟙 P) ^ n)
  [Epi ((𝟙 B) ^ n)] [EffectiveEpi ((𝟙 B) ^ (n * n))] [Epi (F.map ((𝟙 B) ^ (n * n)))]
  (m : F.obj B ⟶ F.obj P) [IsMonHom m] (hm : F.map f ≫ m ≫ F.map d = F.map l)

include hgf hde hm

/-- Faithful field extension and effective scalar quotients descend the unique solution of the polarization equation. -/
theorem existsUnique_homomorphism :
    ∃! r : B ⟶ P, IsMonHom r ∧ f ≫ r ≫ d = l := by
  have hFg : F.map g ≫ F.map f = (𝟙 (F.obj B)) ^ n :=
    (F.map_comp g f).symm.trans ((congrArg F.map hgf).trans (MonoidalScalarPreservation.map_scalar F B n))
  have hFd : F.map d ≫ F.map e = (𝟙 (F.obj P)) ^ n :=
    (F.map_comp d e).symm.trans ((congrArg F.map hde).trans (MonoidalScalarPreservation.map_scalar F P n))
  have hs : F.map ((𝟙 B) ^ (n * n)) ≫ m = F.map (g ≫ l ≫ e) :=
    (congrArg (fun t => t ≫ m) (MonoidalScalarPreservation.map_scalar F B (n * n))).trans
      ((scaled_equation (F.map f) (F.map g) (F.map d) (F.map e) (F.map l) n hFg hFd m hm).trans
        ((congrArg (fun t => F.map g ≫ t) (F.map_comp l e).symm).trans (F.map_comp g (l ≫ e)).symm))
  obtain ⟨r, hr, _⟩ := FaithfulFactorDescent.existsUnique_factor F ((𝟙 B) ^ (n * n)) (g ≫ l ≫ e) m hs
  have : IsMonHom (F.map r) := hr.2.symm ▸ (inferInstance : IsMonHom m)
  have hmon : IsMonHom r := MonoidalHomReflection.isMonHom F r
  have heq : f ≫ r ≫ d = l := by
    apply F.map_injective
    rw [F.map_comp, F.map_comp, hr.2]
    exact hm
  refine ⟨r, ⟨hmon, heq⟩, ?_⟩
  intro t ht
  have : IsMonHom t := ht.1
  exact PullbackCancellation.pullback_injective f d e n hde t r (ht.2.trans heq.symm)

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.FactorDescent
