import OAI.AlgebraicGeometry.Picard.Homomorphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over

/-! # Quotient -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Quotient.Construction

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

universe u

/-- The scheme-theoretic kernel on every test scheme, retaining nilpotents. -/
noncomputable def kernelPoints {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    (q : A ⟶ B) [IsMonHom q] (T : Over S) : Subgroup (T ⟶ A) :=
  (IsMonHom.monoidHom q T).ker

/-- The universal property of the fppf sheaf quotient by the kernel:
sections of every fppf sheaf descend uniquely exactly when invariant under
kernel translation. Via Yoneda this is the coequalizer universal property. -/
def IsFppfQuotientByKernel {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    (q : A ⟶ B) [IsMonHom q] : Prop :=
  ∀ P : (Over S)ᵒᵖ ⥤ Type (u + 1), Presieve.IsSheaf (Scheme.fppfTopology.over S) P →
    ∀ a : P.obj (op A),
      (∀ (T : Over S) (x : T ⟶ A) (k : kernelPoints q T),
        P.map ((k.val * x).op) a = P.map x.op a) →
      ∃! b : P.obj (op B), P.map q.op b = a

set_option backward.isDefEq.respectTransparency.types false in
theorem fppf_singleton_over {S : Scheme.{u}} {A B : Over S}
    (q : A ⟶ B) [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    Sieve.generate (Presieve.singleton q) ∈ (Scheme.fppfTopology.over S) B := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
  erw [← Sieve.arrows_generate_map_eq_functorPushforward, Presieve.map_singleton,
    Sieve.generate_sieve]
  exact Precoverage.generate_mem_toGrothendieck q.left.singleton_mem_fppfPrecoverage

/-- An fppf group homomorphism represents its quotient by its scheme kernel. -/
theorem isFppfQuotientByKernel_of_fppf {S : Scheme.{u}} {A B : Over S}
    [GrpObj A] [GrpObj B] (q : A ⟶ B) [IsMonHom q]
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    IsFppfQuotientByKernel q := by
  intro P hP a hinv
  apply (Presieve.isSheafFor_singleton (P := P)).mp
    (hP.isSheafFor _ (fppf_singleton_over q)) a
  intro T x y hxy
  have hk : x * y⁻¹ ∈ kernelPoints q T := by
    change (x * y⁻¹) ≫ q = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
  have h := hinv T y ⟨x * y⁻¹, hk⟩
  simpa only [inv_mul_cancel_right] using h

/-- Finite locally free, expressed using existing scheme morphism properties. -/
def FiniteLocallyFreeHom {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f

/-- The quotient and finite-locally-free parts of Homomorphisms hold for every smooth
group scheme; properness and ordinarity are unnecessary for these parts. -/
theorem relativeFrobenius_finiteLocallyFree_quotient
    (p : ℕ) (hp : p.Prime) {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) [GrpObj A] [Smooth A.hom] :
    FiniteLocallyFreeHom (Frobenius.Construction.relativeFrobenius p hp hS A).left ∧
      Surjective (Frobenius.Construction.relativeFrobenius p hp hS A).left ∧
      IsFppfQuotientByKernel (Frobenius.Construction.relativeFrobenius p hp hS A) := by
  have : Flat (Frobenius.Construction.relativeFrobenius p hp hS A).left := Homomorphisms.Smooth.Construction.relativeFrobenius_smooth_flat p hp hS A
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩, inferInstance,
    isFppfQuotientByKernel_of_fppf _⟩

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Quotient.Construction
