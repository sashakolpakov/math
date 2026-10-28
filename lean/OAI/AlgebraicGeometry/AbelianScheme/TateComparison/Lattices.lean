import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Functor

/-! # Lattices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Lattices

noncomputable section

/-! The actual Tate preimage lattice is functorial under composition and
contains the source integral Tate image. No coordinate frame is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u
variable {S : Scheme.{u}} {A B C : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C]
  (T : Over S) (q : ℕ) [Fact q.Prime]

theorem rationalTateMap_integral (f : A ⟶ B) [IsMonHom f]
    (x : Add.schemeTateModule A T q) :
    Rational.rationalTateMap (T := T) (q := q) f (1 ⊗ₜ[ℤ_[q]] x) =
      1 ⊗ₜ[ℤ_[q]] (Add.schemeTateMap A T q f x) := by
  simp [Rational.rationalTateMap]

theorem integralTateImage_le_preimage (f : A ⟶ B) [IsMonHom f] :
    Rational.integralTateImage A T q ≤ Rational.isogenyTatePreimage (T := T) (q := q) f := by
  rintro z ⟨x, rfl⟩
  exact ⟨Add.schemeTateMap A T q f x, (rationalTateMap_integral T q f x).symm⟩

theorem isogenyTatePreimage_id :
    Rational.isogenyTatePreimage (T := T) (q := q) (𝟙 A) = Rational.integralTateImage A T q := by
  rw [Rational.isogenyTatePreimage, Functor.rationalTateMap_id]
  rfl

theorem isogenyTatePreimage_comp (f : A ⟶ B) [IsMonHom f]
    (g : B ⟶ C) [IsMonHom g] :
    Rational.isogenyTatePreimage (T := T) (q := q) (f ≫ g) =
      (Rational.isogenyTatePreimage (T := T) (q := q) g).comap
        ((Rational.rationalTateMap (T := T) (q := q) f).restrictScalars ℤ_[q]) := by
  rw [Rational.isogenyTatePreimage, Functor.rationalTateMap_comp]
  rfl

theorem isogenyTatePreimage_mono_comp (f : A ⟶ B) [IsMonHom f]
    (g : B ⟶ C) [IsMonHom g] :
    Rational.isogenyTatePreimage (T := T) (q := q) f ≤
      Rational.isogenyTatePreimage (T := T) (q := q) (f ≫ g) := by
  rw [isogenyTatePreimage_comp]
  exact Submodule.comap_mono (integralTateImage_le_preimage T q g)

theorem framedTateLattice_mono_comp {s : ℕ} (e : Rational.SplitTateFrame s A T q)
    (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g] (v : Fin s × Bool) :
    Rational.framedTateLattice e f v ≤ Rational.framedTateLattice e (f ≫ g) v :=
  Submodule.map_mono (Submodule.map_mono (isogenyTatePreimage_mono_comp T q f g))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Lattices
