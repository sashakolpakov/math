import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SmithDeterminant
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ShortComplexColength
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Short Complex Determinant -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ShortComplexDeterminant

noncomputable section

/-! The Euler characteristic of a generically exact three-term free complex
over a principal ideal domain is the difference of two determinant orders. -/

open _root_.Module
open scoped Classical

universe u v w w'

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {A B C : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]
  {ι : Type w} {κ : Type w'} [Fintype ι] [Fintype κ]

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ShortComplexColength

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem coprod_injective (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : g.comp f = 0)
    (hf : Function.Injective f) (t : C →ₗ[R] B) (ht : Function.Injective (g.comp t)) :
    Function.Injective (f.coprod t) := by
  rintro ⟨a, c⟩ ⟨a', c'⟩ he
  have hc : c = c' := by
    apply ht
    change g (t c) = g (t c')
    have hg := congrArg g he
    change g (f a + t c) = g (f a' + t c') at hg
    simpa only [map_add, show g (f a) = 0 from DFunLike.congr_fun h a,
      show g (f a') = 0 from DFunLike.congr_fun h a', zero_add] using hg
  have ha : a = a' := hf (by simpa [LinearMap.coprod_apply, hc] using he)
  exact Prod.ext ha hc

theorem order_comparison (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : g.comp f = 0)
    (hf : Function.Injective f) (t : C →ₗ[R] B) (ht : Function.Injective (g.comp t))
    (b : Basis ι R (A × C)) (c : Basis ι R B) (e : Basis κ R C) :
    Ring.ord R (LinearMap.toMatrix b c (f.coprod t)).det +
        Module.length R (C ⧸ g.range) =
      Module.length R (g.ker ⧸ (ShortComplexColength.toCycles R f g h).range) +
        Ring.ord R (g.comp t).det := by
  have he := ShortComplexColength.length_comparison R f g h t ht
  rw [SmithDeterminant.cokernel_length_matrix R b c _
    (coprod_injective R f g h hf t ht),
    SmithDeterminant.cokernel_length_det R e _ ht] at he
  exact he

theorem euler_eq (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : g.comp f = 0)
    (hf : Function.Injective f) (t : C →ₗ[R] B) (ht : Function.Injective (g.comp t))
    (b : Basis ι R (A × C)) (c : Basis ι R B) (e : Basis κ R C) :
    ((Module.length R (C ⧸ g.range)).toNat : ℚ) -
        ((Module.length R (g.ker ⧸ (ShortComplexColength.toCycles R f g h).range)).toNat : ℚ) =
      ((Ring.ord R (g.comp t).det).toNat : ℚ) -
        ((Ring.ord R (LinearMap.toMatrix b c (f.coprod t)).det).toNat : ℚ) := by
  have hj := SmithDeterminant.cokernel_length_ne_top R b c _
    (coprod_injective R f g h hf t ht)
  have hgt := SmithDeterminant.cokernel_length_ne_top R e e _ ht
  have hH : Module.length R (g.ker ⧸ (ShortComplexColength.toCycles R f g h).range) ≠ ⊤ :=
    ne_top_of_le_ne_top hj (Module.length_le_of_injective
      (ShortComplexColength.homologyToCokernel R f g h t) (ShortComplexColength.homologyToCokernel_injective R f g h t ht))
  have hle : (g.comp t).range ≤ g.range := by
    rintro x ⟨y, rfl⟩
    exact ⟨t y, rfl⟩
  have h₀ : Module.length R (C ⧸ g.range) ≠ ⊤ :=
    ne_top_of_le_ne_top hgt (Module.length_le_of_surjective
      ((g.comp t).range.mapQ g.range LinearMap.id hle) (by
        intro x
        obtain ⟨y, rfl⟩ := g.range.mkQ_surjective x
        exact ⟨(g.comp t).range.mkQ y, rfl⟩))
  have he := congrArg (fun n : ℕ∞ => (n.toNat : ℚ)) (ShortComplexColength.length_comparison R f g h t ht)
  rw [ENat.toNat_add hj h₀, ENat.toNat_add hH hgt, Nat.cast_add, Nat.cast_add,
    SmithDeterminant.cokernel_length_matrix R b c _
      (coprod_injective R f g h hf t ht),
    SmithDeterminant.cokernel_length_det R e _ ht] at he
  linarith

theorem native_order_comparison (S : CategoryTheory.ShortComplex (ModuleCat.{v} R))
    (hf : Function.Injective S.f) (t : S.X₃ →ₗ[R] S.X₂)
    (ht : Function.Injective (S.g.hom.comp t))
    (b : Basis ι R (S.X₁ × S.X₃)) (c : Basis ι R S.X₂) (e : Basis κ R S.X₃) :
    Ring.ord R (LinearMap.toMatrix b c (S.f.hom.coprod t)).det +
        Module.length R (S.X₃ ⧸ S.g.hom.range) =
      Module.length R S.homology + Ring.ord R (S.g.hom.comp t).det := by
  rw [S.moduleCatHomologyIso.toLinearEquiv.length_eq]
  exact order_comparison R S.f.hom S.g.hom (ModuleCat.hom_ext_iff.mp S.zero) hf t ht b c e

theorem native_euler_eq (S : CategoryTheory.ShortComplex (ModuleCat.{v} R))
    (hf : Function.Injective S.f) (t : S.X₃ →ₗ[R] S.X₂)
    (ht : Function.Injective (S.g.hom.comp t))
    (b : Basis ι R (S.X₁ × S.X₃)) (c : Basis ι R S.X₂) (e : Basis κ R S.X₃) :
    ((Module.length R (S.X₃ ⧸ S.g.hom.range)).toNat : ℚ) -
        ((Module.length R S.homology).toNat : ℚ) =
      ((Ring.ord R (S.g.hom.comp t).det).toNat : ℚ) -
        ((Ring.ord R (LinearMap.toMatrix b c (S.f.hom.coprod t)).det).toNat : ℚ) := by
  rw [S.moduleCatHomologyIso.toLinearEquiv.length_eq]
  exact euler_eq R S.f.hom S.g.hom (ModuleCat.hom_ext_iff.mp S.zero) hf t ht b c e

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ShortComplexDeterminant
