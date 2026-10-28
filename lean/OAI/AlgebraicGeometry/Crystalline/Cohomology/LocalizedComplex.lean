import OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationExactnessOf
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Localized Complex -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizedComplex.LocalizedComplexExactness

noncomputable section

/-!
# Exactness of actual module complexes checked on principal opens

The algebraic image-descent criterion applies to short complexes and to
every degree of an actual homological complex. This is the local-to-global
exactness step for the affine Čech computation.
-/

open _root_.CategoryTheory

universe u v

variable (R ι : Type u) [CommRing R] (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)

include hs

theorem shortComplex (C : ShortComplex (ModuleCat.{u} R)) (CL : ι → ShortComplex (ModuleCat.{u} R))
    (φ : ∀ i, C ⟶ CL i)
    [∀ i, IsLocalizedModule (Submonoid.powers (s i)) ((φ i).τ₁).hom]
    [∀ i, IsLocalizedModule (Submonoid.powers (s i)) ((φ i).τ₂).hom]
    (hCL : ∀ i, (CL i).Exact) : C.Exact := by
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact C).mpr
  exact LocalizationExactnessOf.LocalizationExactness.exact_of_localized R ι C.X₁ C.X₂ C.X₃ C.f.hom C.g.hom
    (congrArg (fun h : C.X₁ ⟶ C.X₃ => h.hom) C.zero) s
    (fun i => (CL i).X₁) (fun i => (CL i).X₂) (fun i => (CL i).X₃)
    (fun i => ((φ i).τ₁).hom) (fun i => ((φ i).τ₂).hom) (fun i => ((φ i).τ₃).hom)
    (fun i => (CL i).f.hom) (fun i => (CL i).g.hom)
    (fun i x => (congrArg (fun h : C.X₁ ⟶ (CL i).X₂ => h.hom x) (φ i).comm₁₂).symm)
    (fun i x => congrArg (fun h : C.X₂ ⟶ (CL i).X₃ => h.hom x) (φ i).comm₂₃)
    hs (fun i => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (CL i)).mp (hCL i))

theorem exactAt {κ : Type v} (c : ComplexShape κ)
    (K : HomologicalComplex (ModuleCat.{u} R) c) (KL : ι → HomologicalComplex (ModuleCat.{u} R) c)
    (φ : ∀ i, K ⟶ KL i)
    [∀ i j, IsLocalizedModule (Submonoid.powers (s i)) ((φ i).f j).hom]
    (j : κ) (hKL : ∀ i, (KL i).ExactAt j) : K.ExactAt j := by
  have : ∀ i, IsLocalizedModule (Submonoid.powers (s i))
      (((HomologicalComplex.shortComplexFunctor (ModuleCat R) c j).map (φ i)).τ₁).hom := by
    intro i
    change IsLocalizedModule (Submonoid.powers (s i)) ((φ i).f (c.prev j)).hom
    infer_instance
  have : ∀ i, IsLocalizedModule (Submonoid.powers (s i))
      (((HomologicalComplex.shortComplexFunctor (ModuleCat R) c j).map (φ i)).τ₂).hom := by
    intro i
    change IsLocalizedModule (Submonoid.powers (s i)) ((φ i).f j).hom
    infer_instance
  exact shortComplex R ι s hs (K.sc j) (fun i => (KL i).sc j)
    (fun i => (HomologicalComplex.shortComplexFunctor (ModuleCat R) c j).map (φ i)) hKL

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizedComplex.LocalizedComplexExactness
