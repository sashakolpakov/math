import Mathlib.Algebra.Category.ModuleCat.Projective
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.LocalDualResolutionExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.DualCokernelResidue
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ResolutionBasic

/-! # Augmented Dual Projective Resolution -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AugmentedDualProjectiveResolution

noncomputable section

/-! Identify the degree-zero cokernel and use exactness in positive degrees to build the actual projective resolution carried by the dual cochain model. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def projectiveResolutionOfCokernelIso
    {V : Type u} [Category.{v} V] [Abelian V]
    (K : ChainComplex V ℕ) (hproj : ∀ n, Projective (K.X n))
    (hexact : ∀ n, 0 < n → K.ExactAt n) {Z : V} (E : cokernel (K.d 1 0) ≅ Z) :
    HilbertConstruction.Projective.ResolutionBasic.ProjectiveResolution Z := by
  let p := cokernel.π (K.d 1 0) ≫ E.hom
  have hp : K.d 1 0 ≫ p = 0 := by
    dsimp only [p]
    rw [← Category.assoc, cokernel.condition, zero_comp]
  let π := (ChainComplex.toSingle₀Equiv K Z).symm ⟨p, hp⟩
  have hπzero : π.f 0 = p := ChainComplex.toSingle₀Equiv_symm_apply_f_zero p hp
  have hpExact : (ShortComplex.mk (K.d 1 0) p hp).Exact := by
    let e : ShortComplex.mk (K.d 1 0) (cokernel.π (K.d 1 0)) (cokernel.condition _) ≅
        ShortComplex.mk (K.d 1 0) p hp :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) E (by simp) (by simp [p])
    exact ShortComplex.exact_of_iso e (ShortComplex.cokernelSequence_exact (K.d 1 0))
  have : Epi p := inferInstanceAs (Epi (cokernel.π (K.d 1 0) ≫ E.hom))
  have hπ : QuasiIso π := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · change (ShortComplex.mk (K.d 1 0) (π.f 0) _).Exact ∧ Epi (π.f 0)
        simpa only [hπzero] using (And.intro hpExact (inferInstance : Epi p))
      all_goals first | rfl | simp
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' π (n + 1)
        (ChainComplex.exactAt_succ_single_obj _ _)]
      exact hexact (n + 1) (Nat.succ_pos n)⟩
  exact { complex := K, projective := hproj, π := π, quasiIso := hπ }

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

def minimalDualProjectiveResolution
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (g : ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (hbound : ∀ q, g < q → IsZero (C.X q))
    (rs : List R) (hlen : rs.length = g) (hreg : Regular.SequenceBasic.RingTheory.Sequence.IsRegular R rs)
    (hgen : Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal R) (hfield : Cochain.FieldSupport.CochainFieldSupport C (maximalIdeal R))
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2))
    (e : R ≃ₗ[R] Q.complex.X₁) (hI : Q.firstDifferentialIdeal = maximalIdeal R) :
    HilbertConstruction.Projective.ResolutionBasic.ProjectiveResolution (ModuleCat.of R (ResidueField R)) := by
  let K : ChainComplex (ModuleCat.{u} R) ℕ := HilbertConstruction.Module.DualFunctor.dualModuleComplex C
  have hproj (n : ℕ) : Projective (K.X n) := by
    have : Module.Finite R (C.X n) := hfin n
    have : Module.Free R (C.X n) := hfree n
    have : Module.Free R (Module.Dual R (C.X n)) := inferInstance
    have : Module.Projective R (Module.Dual R (C.X n)) := inferInstance
    exact (ModuleCat.of R (Module.Dual R (C.X n))).projective_of_categoryTheory_projective
  exact projectiveResolutionOfCokernelIso K hproj
    (Regular.LocalDualResolutionExactness.regularLocal_dualComplex_exact_positive C g hfin hfree hbound rs hlen hreg hgen hfield)
    (Q.originalDualCokernelResidueIso e hI)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AugmentedDualProjectiveResolution
