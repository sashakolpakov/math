import OAI.AlgebraicGeometry.Picard.Homomorphisms.Kernel
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Affine
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-! # Diagonalizable -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Diagonalizable

/-!
# Homomorphisms: multiplicative p-torsion maps into the Frobenius kernel

For a split diagonalizable group with character group killed by p, relative
Frobenius is the trivial group-scheme morphism. Consequently its group maps
to any group scheme factor through the scheme-theoretic Frobenius kernel.
No restriction to reduced test rings or geometric points is made.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (p : ℕ) (hp : p.Prime)

theorem relativeFrobenius_eq_one_of_absolute {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) [GrpObj A]
    (hF : Frobenius.Construction.absoluteFrobenius p hp A.left (Frobenius.Construction.prime_eq_zero_of_map p hS A.hom) =
      (1 : A ⟶ A).left ≫ Frobenius.Construction.absoluteFrobenius p hp A.left (Frobenius.Construction.prime_eq_zero_of_map p hS A.hom)) :
    Frobenius.Construction.relativeFrobenius p hp hS A = 1 := by
  have h : Frobenius.Construction.relativeFrobenius p hp hS A = (1 : A ⟶ A) ≫ Frobenius.Construction.relativeFrobenius p hp hS A := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · dsimp only [Frobenius.Construction.relativeFrobenius, Over.homMk_left, Over.comp_left]
      erw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
      exact hF
    · dsimp only [Frobenius.Construction.relativeFrobenius, Over.homMk_left, Over.comp_left]
      erw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
      exact (1 : A ⟶ A).w.symm
  exact h.trans (MonObj.one_comp (Frobenius.Construction.relativeFrobenius p hp hS A))

variable (R M : Type u) [CommRing R] [CommGroup M]

/-- The split diagonalizable group with character group `M`. -/
noncomputable abbrev diagonalizableGroup : Over (Spec (CommRingCat.of R)) :=
  (Spec (CommRingCat.of (MonoidAlgebra R M))).asOver (Spec (CommRingCat.of R))

theorem diagonalizableGroup_one_left :
    (1 : diagonalizableGroup R M ⟶ diagonalizableGroup R M).left =
      Spec.map (CommRingCat.ofHom ((algebraMap R (MonoidAlgebra R M)).comp
        (Bialgebra.counitAlgHom R (MonoidAlgebra R M)).toRingHom)) := by
  rw [Hom.one_def, Over.comp_left, one_spec_asOver_spec_left]
  change Spec.map (CommRingCat.ofHom (algebraMap R (MonoidAlgebra R M))) ≫ _ = _
  erw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem prime_eq_zero_monoidAlgebra (hR : (p : R) = 0) :
    (p : MonoidAlgebra R M) = 0 := by
  simpa only [map_natCast, map_zero] using congrArg (algebraMap R (MonoidAlgebra R M)) hR

/-- Frobenius on the coordinate Hopf algebra is unchanged by augmentation
followed by the structural map when every character is killed by p. -/
theorem monoidAlgebra_frobenius_counit (hR : (p : R) = 0) (hM : ∀ m : M, m ^ p = 1) :
    Frobenius.Construction.powerRingHom p hp (MonoidAlgebra R M) (prime_eq_zero_monoidAlgebra p R M hR) =
      ((algebraMap R (MonoidAlgebra R M)).comp
        (Bialgebra.counitAlgHom R (MonoidAlgebra R M)).toRingHom).comp
        (Frobenius.Construction.powerRingHom p hp (MonoidAlgebra R M) (prime_eq_zero_monoidAlgebra p R M hR)) := by
  apply MonoidAlgebra.ringHom_ext
  · intro r
    simp [MonoidAlgebra.single_pow]
  · intro m
    simp [MonoidAlgebra.single_pow, hM]

/-- Scheme-level vanishing of relative Frobenius on split multiplicative
groups with p-torsion character group. -/
theorem diagonalizableGroup_relativeFrobenius (hR : (p : R) = 0)
    (hM : ∀ m : M, m ^ p = 1) :
    Frobenius.Construction.relativeFrobenius p hp (Homomorphisms.Affine.Construction.prime_eq_zero_spec p R hR) (diagonalizableGroup R M) = 1 := by
  apply relativeFrobenius_eq_one_of_absolute
  rw [diagonalizableGroup_one_left]
  change Frobenius.Construction.absoluteFrobenius p hp (Spec (CommRingCat.of (MonoidAlgebra R M))) _ = _
  erw [Homomorphisms.Affine.Construction.absoluteFrobenius_spec p hp (MonoidAlgebra R M)
    (prime_eq_zero_monoidAlgebra p R M hR)]
  erw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (monoidAlgebra_frobenius_counit p hp R M hR hM)

/-- Naturality carries a group scheme with trivial Frobenius into the
scheme-theoretic Frobenius kernel of any target group scheme. -/
theorem factors_kernel_of_trivial_relativeFrobenius {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (D A : Over S) [GrpObj D] [GrpObj A]
    (hD : Frobenius.Construction.relativeFrobenius p hp hS D = 1) (f : D ⟶ A) [IsMonHom f] :
    ∃! k : D ⟶ Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p hp hS A),
      k ≫ Kernel.Construction.kernelInclusion (Frobenius.Construction.relativeFrobenius p hp hS A) = f := by
  apply (Kernel.Construction.kernelScheme_universal _ D f).mp
  let : GrpObj ((Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).obj D) :=
    Homomorphisms.Group.Construction.frobeniusTwist_grp p hp hS D
  let : GrpObj ((Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).obj A) :=
    Homomorphisms.Group.Construction.frobeniusTwist_grp p hp hS A
  have hf' : IsMonHom ((Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map f) :=
    Functor.map.instIsMonHom (F := Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS))
      (f := f) D A
  have h := (Homomorphisms.Group.Construction.relativeFrobeniusNat p hp hS).naturality f
  change f ≫ Frobenius.Construction.relativeFrobenius p hp hS A = Frobenius.Construction.relativeFrobenius p hp hS D ≫
    (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map f at h
  rw [hD] at h
  exact h.trans (by
    let q : Frobenius.Construction.frobeniusTwist p hp hS D ⟶ Frobenius.Construction.frobeniusTwist p hp hS A :=
      (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map f
    have : IsMonHom q := hf'
    exact MonObj.one_comp q)

/-- Every group map from a split diagonalizable p-torsion group into `A`
factors uniquely through the actual relative Frobenius kernel. -/
theorem diagonalizableGroup_factors_frobeniusKernel (hR : (p : R) = 0)
    (hM : ∀ m : M, m ^ p = 1) (A : Over (Spec (CommRingCat.of R))) [GrpObj A]
    (f : diagonalizableGroup R M ⟶ A) [IsMonHom f] :
    ∃! k : diagonalizableGroup R M ⟶
        Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p hp (Homomorphisms.Affine.Construction.prime_eq_zero_spec p R hR) A),
      k ≫ Kernel.Construction.kernelInclusion (Frobenius.Construction.relativeFrobenius p hp (Homomorphisms.Affine.Construction.prime_eq_zero_spec p R hR) A) = f :=
  factors_kernel_of_trivial_relativeFrobenius p hp _ _ A
    (diagonalizableGroup_relativeFrobenius p hp R M hR hM) f

/-- The split group μ_p^g, as the spectrum of the group Hopf algebra of
the character group `(ℤ/pℤ)^g`. -/
noncomputable abbrev splitMultiplicativePTorsion (g : ℕ) : Over (Spec (CommRingCat.of R)) :=
  diagonalizableGroup R (ULift.{u} (Multiplicative (Fin g → ZMod p)))

/-- In particular, every group-scheme map from μ_p^g factors uniquely
through the Frobenius kernel, on all test schemes. -/
theorem splitMultiplicativePTorsion_factors_frobeniusKernel
    (hR : (p : R) = 0) (g : ℕ) (A : Over (Spec (CommRingCat.of R))) [GrpObj A]
    (f : splitMultiplicativePTorsion p R g ⟶ A) [IsMonHom f] :
    ∃! k : splitMultiplicativePTorsion p R g ⟶
        Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p hp (Homomorphisms.Affine.Construction.prime_eq_zero_spec p R hR) A),
      k ≫ Kernel.Construction.kernelInclusion (Frobenius.Construction.relativeFrobenius p hp (Homomorphisms.Affine.Construction.prime_eq_zero_spec p R hR) A) = f := by
  apply diagonalizableGroup_factors_frobeniusKernel p hp R _ hR _ A f
  intro m
  apply ULift.ext
  change p • m.down.toAdd = 0
  ext i
  simp [nsmul_eq_mul]

end Construction

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Diagonalizable
