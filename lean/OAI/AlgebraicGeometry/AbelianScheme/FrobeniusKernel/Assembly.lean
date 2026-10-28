import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BlockProducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionFunctoriality

/-! # Assembly -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Assembly.Construction

noncomputable section

/-!
The full kernel is constructed as the product of its actual chosen and
opposite block schemes and embedded in the abelian scheme through its
scheme-theoretic torsion. The construction proves finite local freeness,
closedness, the group law, and the multiplier-torsion bound.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {g : ℕ} {S : Scheme.{u}} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

/-- The zero-fiber representing equivalence proves that the torsion
inclusion preserves the group law on every test scheme. -/
instance torsionInclusion_isMonHom (n : ℕ) : IsMonHom (A.torsionInclusion n) where
  one_hom := by
    have h := congrArg (fun x : A.torsionPoints n (𝟙_ (Over S)) => x.val)
      (((A.torsionSchemeYonedaIso n).hom.app (op (𝟙_ (Over S)))).hom.map_one)
    change (1 : 𝟙_ (Over S) ⟶ A.torsionScheme n) ≫ A.torsionInclusion n = 1 at h
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h
  mul_hom := by
    let T := A.torsionScheme n
    let i := A.torsionInclusion n
    have h := congrArg (fun x : A.torsionPoints n (T ⊗ T) => x.val)
      (((A.torsionSchemeYonedaIso n).hom.app (op (T ⊗ T))).hom.map_mul (fst T T) (snd T T))
    change (fst T T * snd T T) ≫ i = (fst T T ≫ i) * (snd T T ≫ i) at h
    have hp : lift (fst T T ≫ i) (snd T T ≫ i) = i ⊗ₘ i := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, tensorHom_fst]; rfl
      · simp only [lift_snd, tensorHom_snd]; rfl
    exact (congrArg (fun f => f ≫ i) (MonObj.mul_eq_mul (M := T))).trans
      (h.trans (congrArg (fun f => f ≫ μ[A.scheme]) hp))

/-- The torsion group scheme, bundled for its block decomposition. -/
abbrev torsionGroup (n : ℕ) : Grp (Over S) := Grp.mk (A.torsionScheme n)

/-- Assemble the block subgroups and their actual inclusion into A. -/
def fullKernelToAbelian (n k : ℕ) (H B : Fin k → Grp (Over S))
    (i : ∀ v, H v ⟶ B v) (split : torsionGroup A n ≅ BlockProducts.Construction.groupBlockProduct k B) :
    (BlockProducts.Construction.groupBlockProduct k H).X ⟶ A.scheme :=
  (BlockProducts.Construction.fullBlockKernelInclusion k H B i (torsionGroup A n) split).hom.hom ≫ A.torsionInclusion n

instance fullKernelToAbelian_isMonHom (n k : ℕ) (H B : Fin k → Grp (Over S))
    (i : ∀ v, H v ⟶ B v) (split : torsionGroup A n ≅ BlockProducts.Construction.groupBlockProduct k B) :
    IsMonHom (fullKernelToAbelian A n k H B i split) := by
  unfold fullKernelToAbelian
  infer_instance

theorem fullKernelToAbelian_closed (n k : ℕ) (H B : Fin k → Grp (Over S))
    (i : ∀ v, H v ⟶ B v) (hi : ∀ v, IsClosedImmersion (i v).hom.hom.left)
    (split : torsionGroup A n ≅ BlockProducts.Construction.groupBlockProduct k B) :
    IsClosedImmersion (fullKernelToAbelian A n k H B i split).left := by
  have := BlockProducts.Construction.fullBlockKernelInclusion_closed k H B i hi (torsionGroup A n) split
  change IsClosedImmersion
    ((BlockProducts.Construction.fullBlockKernelInclusion k H B i (torsionGroup A n) split).hom.hom.left ≫
      (A.torsionInclusion n).left)
  infer_instance

/-- The assembled kernel is killed by the single total multiplier n on
all test schemes, including infinitesimal tests. -/
theorem fullKernelToAbelian_killed (n k : ℕ) (H B : Fin k → Grp (Over S))
    (i : ∀ v, H v ⟶ B v) (split : torsionGroup A n ≅ BlockProducts.Construction.groupBlockProduct k B)
    (T : Over S) (x : T ⟶ (BlockProducts.Construction.groupBlockProduct k H).X) :
    (x ≫ fullKernelToAbelian A n k H B i split) ^ n = 1 := by
  change (x ≫ (BlockProducts.Construction.fullBlockKernelInclusion k H B i (torsionGroup A n) split).hom.hom ≫
    A.torsionInclusion n) ^ n = 1
  rw [← Category.assoc, ← MonObj.comp_pow, A.torsionInclusion_pow, MonObj.comp_one]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Assembly.Construction
