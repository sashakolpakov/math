import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Bicomplex Pairing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexPairing

noncomputable section

/-! A bilinear pairing of bidegrees induces a bilinear pairing of the
actual categorical total complexes. The construction uses only their
coproduct universal properties. -/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [CommRing R]
  (K L M : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))
  [K.HasTotal (.up ℕ)] [L.HasTotal (.up ℕ)] [M.HasTotal (.up ℕ)]
  (μ : ∀ p q r s, (K.X p).X q →ₗ[R] (L.X r).X s →ₗ[R] (M.X (p + r)).X (q + s))

def rightDesc (n m p q : ℕ) (hpq : p + q = n) :
    (L.total (.up ℕ)).X m →ₗ[R] (K.X p).X q →ₗ[R] (M.total (.up ℕ)).X (n + m) :=
  (L.totalDesc (c₁₂ := .up ℕ) fun r s hrs =>
    ModuleCat.ofHom (((μ p q r s).compr₂
      (M.ιTotal (.up ℕ) (p + r) (q + s) (n + m) (by
        change (p + r) + (q + s) = n + m
        change r + s = m at hrs
        omega)).hom).flip)).hom

def totalPairing (n m : ℕ) :
    (K.total (.up ℕ)).X n →ₗ[R] (L.total (.up ℕ)).X m →ₗ[R] (M.total (.up ℕ)).X (n + m) :=
  (K.totalDesc (c₁₂ := .up ℕ) fun p q hpq =>
    ModuleCat.ofHom (rightDesc K L M μ n m p q hpq).flip).hom

theorem totalPairing_ι (n m p q r s : ℕ) (hpq : p + q = n) (hrs : r + s = m)
    (x : (K.X p).X q) (y : (L.X r).X s) :
    totalPairing K L M μ n m (K.ιTotal (.up ℕ) p q n hpq x)
        (L.ιTotal (.up ℕ) r s m hrs y) =
      M.ιTotal (.up ℕ) (p + r) (q + s) (n + m) (by
        change (p + r) + (q + s) = n + m
        omega) (μ p q r s x y) := by
  have h₁ := ConcreteCategory.congr_hom (K.ι_totalDesc (c₁₂ := .up ℕ) (i₁₂ := n)
    (fun p q hpq => ModuleCat.ofHom (rightDesc K L M μ n m p q hpq).flip)
    p q hpq) x
  change totalPairing K L M μ n m (K.ιTotal (.up ℕ) p q n hpq x) =
    (rightDesc K L M μ n m p q hpq).flip x at h₁
  rw [h₁]
  change rightDesc K L M μ n m p q hpq (L.ιTotal (.up ℕ) r s m hrs y) x = _
  have h₂ := ConcreteCategory.congr_hom (L.ι_totalDesc (c₁₂ := .up ℕ) (i₁₂ := m)
    (fun r s hrs => ModuleCat.ofHom (((μ p q r s).compr₂
      (M.ιTotal (.up ℕ) (p + r) (q + s) (n + m) (by
        change (p + r) + (q + s) = n + m
        change r + s = m at hrs
        omega)).hom).flip)) r s hrs) y
  exact DFunLike.congr_fun h₂ x

omit [M.HasTotal (.up ℕ)] in
theorem bilinear_ext {Z : Type v} [AddCommGroup Z] [Module R Z] (n m : ℕ)
    {f g : (K.total (.up ℕ)).X n →ₗ[R] (L.total (.up ℕ)).X m →ₗ[R] Z}
    (h : ∀ p q r s (hpq : p + q = n) (hrs : r + s = m)
      (x : (K.X p).X q) (y : (L.X r).X s),
      f (K.ιTotal (.up ℕ) p q n hpq x) (L.ιTotal (.up ℕ) r s m hrs y) =
        g (K.ιTotal (.up ℕ) p q n hpq x) (L.ιTotal (.up ℕ) r s m hrs y)) : f = g := by
  have hf : (ModuleCat.ofHom f : (K.total (.up ℕ)).X n ⟶
      ModuleCat.of R ((L.total (.up ℕ)).X m →ₗ[R] Z)) = ModuleCat.ofHom g := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hg : (ModuleCat.ofHom (f (K.ιTotal (.up ℕ) p q n hpq x)) :
        (L.total (.up ℕ)).X m ⟶ ModuleCat.of R Z) =
          ModuleCat.ofHom (g (K.ιTotal (.up ℕ) p q n hpq x)) := by
      apply HomologicalComplex₂.total.hom_ext
      intro r s hrs
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      exact h p q r s hpq hrs x y
    exact congrArg ModuleCat.Hom.hom hg
  exact congrArg ModuleCat.Hom.hom hf

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexPairing
