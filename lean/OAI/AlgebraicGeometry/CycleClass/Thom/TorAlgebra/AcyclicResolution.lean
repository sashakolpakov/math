import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Acyclic Resolution -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.AcyclicResolution

noncomputable section

/-! Applying a right-exact functor to a projective resolution still
gives a projective resolution when that particular object has vanishing
higher derived functors. Global exactness of the functor is unnecessary. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesProjectiveObjects] [PreservesFiniteColimits F]
  {X : C} (P : ProjectiveResolution X)

def mappedComplex : ChainComplex D ℕ :=
  (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex

omit [EnoughProjectives C] [F.PreservesProjectiveObjects] [PreservesFiniteColimits F] in
theorem mapped_zero_comp : (mappedComplex F P).d 1 0 ≫ F.map (P.π.f 0) = 0 := by
  change F.map (P.complex.d 1 0) ≫ F.map (P.π.f 0) = 0
  rw [← F.map_comp, P.complex_d_comp_π_f_zero, F.map_zero]

omit [EnoughProjectives C] [F.PreservesProjectiveObjects] in
theorem mapped_exact_zero :
    (ShortComplex.mk ((mappedComplex F P).d 1 0) (F.map (P.π.f 0)) (mapped_zero_comp F P)).Exact :=
  P.exact₀.map_of_epi_of_preservesCokernel F inferInstance inferInstance

variable (hv : ∀ n, IsZero ((F.leftDerived (n + 1)).obj X))

omit [F.PreservesProjectiveObjects] [PreservesFiniteColimits F] in
include hv in
theorem mapped_exact_succ (n : ℕ) : (mappedComplex F P).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hv n).of_iso (P.isoLeftDerivedObj F (n + 1)).symm

def resolution : ProjectiveResolution (F.obj X) where
  complex := mappedComplex F P
  projective n := Functor.PreservesProjectiveObjects.projective_obj (P.projective n)
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨F.map (P.π.f 0), mapped_zero_comp F P⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).mpr
          ⟨mapped_exact_zero F P, inferInstance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [mappedComplex]) (by simp)
      all_goals first | rfl | simp [mappedComplex]
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact mapped_exact_succ F P hv n
      · exact ChainComplex.exactAt_succ_single_obj _ n⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.AcyclicResolution
