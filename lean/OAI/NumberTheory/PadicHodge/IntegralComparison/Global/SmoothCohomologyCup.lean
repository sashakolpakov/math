import OAI.NumberTheory.PadicHodge.IntegralComparison.ManifoldWedgeLeibniz
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CupNaturality
import OAI.Analysis.DifferentialForms.Manifold.ClosedPullback

/-! # Smooth Cohomology Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.SmoothCohomologyCup

noncomputable section

/-! The native global smooth de Rham cohomology product and its
normalization on actual closed forms. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def cup (p q : ℕ) :
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).X p →ₗ[ℂ] (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).X q →ₗ[ℂ]
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).X (p + q) :=
  RationalDeRham.SmoothProduct.Wedge.smoothWedge p q

theorem degreeCast_eq {n m : ℕ} (h : n = m) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    Cochain.CohomologyCup.degreeCast (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) h a =
      AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldDegreeCast h a := by
  subst m
  rfl

theorem cupInto_eq (p q k : ℕ) (h : p + q = k)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) :
    Cochain.CohomologyCup.cupInto (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) (cup E M) p q k h a b =
      AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldDegreeCast h (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b) := by
  subst k
  rfl

theorem differential_cup (p q : ℕ) (a : (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).X p)
    (b : (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).X q) :
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).d (p + q) (p + q + 1) (cup E M p q a b) =
      Cochain.CohomologyCup.cupInto (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) (cup E M)
        (p + 1) q (p + q + 1) (by omega) ((Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).d p (p + 1) a) b +
      (-1 : ℤ) ^ p • Cochain.CohomologyCup.cupInto (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) (cup E M)
        p (q + 1) (p + q + 1) (by omega) a ((Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).d q (q + 1) b) := by
  simp only [Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex_d]
  exact (ManifoldWedgeLeibniz.Smooth.manifold_d_wedge a b).trans
    (congrArg₂ (fun x y => x + (-1 : ℤ) ^ p • y)
      (cupInto_eq E M (p + 1) q (p + q + 1) (by omega) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) b).symm
      (cupInto_eq E M p (q + 1) (p + q + 1) (by omega) a (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b)).symm)

def cohomologyCup (p q : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M p →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M q →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M (p + q) :=
  Cochain.CohomologyCup.cohomologyCup (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) (cup E M)
    (differential_cup E M) p q

def closedCycle (n : ℕ) : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n →ₗ[ℂ] Module.CochainClasses.cycles (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n where
  toFun a := ⟨a.val, by
    change (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).d n (n + 1) a.val = 0
    rw [Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex_d]
    exact a.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem closedFormsIso_cycle (n : ℕ) (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) :
    (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso E M n).hom
        ((Module.CochainClassNaturality.cyclesIso (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n).hom (closedCycle E M n a)) = a := by
  apply Subtype.ext
  exact (Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamClosedFormsIso_hom_coe (E := E) (M := M) n
    ((Module.CochainClassNaturality.cyclesIso (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n).hom (closedCycle E M n a))).trans
      (ConcreteCategory.congr_hom (Module.CochainClassNaturality.cyclesIso_hom_i (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n)
        (closedCycle E M n a))

theorem class_closedCycle (n : ℕ) (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) :
    Module.CochainClasses.classMap (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n (closedCycle E M n a) =
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n a := by
  let z := (Module.CochainClassNaturality.cyclesIso (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n).hom (closedCycle E M n a)
  have h := ConcreteCategory.congr_hom (Module.CochainClassNaturality.classMap_eq (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n)
    (closedCycle E M n a)
  have h' := ConcreteCategory.congr_hom (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso_comp_class E M n) z
  change Module.CochainClasses.classMap (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n (closedCycle E M n a) =
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).homologyπ n z at h
  change Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n ((Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso E M n).hom z) =
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).homologyπ n z at h'
  rw [show (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso E M n).hom z = a from closedFormsIso_cycle E M n a] at h'
  exact h.trans h'.symm

theorem cup_formClass (p q : ℕ) (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    cohomologyCup E M p q (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M p a) (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M q b) =
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M (p + q) (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge a b) := by
  rw [← class_closedCycle E M p a, ← class_closedCycle E M q b]
  exact (Cochain.CohomologyCup.cup_class (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) (cup E M)
    (differential_cup E M) p q (closedCycle E M p a) (closedCycle E M q b)).trans
      (class_closedCycle E M (p + q) (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge a b))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.SmoothCohomologyCup
