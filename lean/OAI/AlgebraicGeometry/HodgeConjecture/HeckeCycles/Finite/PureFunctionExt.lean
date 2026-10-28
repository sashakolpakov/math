import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TensorRepresentatives
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedTensorExpansion

/-! # Pure Function Ext -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PureFunctionExt.CM

/-! Linear maps on the actual finite Schwartz functions are determined
by their values on restricted pure test functions. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
  {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem ext (A B : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ[ℂ] V)
    (h : ∀ (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
      (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v),
      A (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf)) =
        B (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf))) : A = B := by
  apply LinearMap.ext
  intro φ
  obtain ⟨t, rfl⟩ := TensorRepresentatives.CM.evaluation_surjective F N φ
  obtain ⟨n, c, f, hf, rfl⟩ := RestrictedTensorExpansion.CM.expansion (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) t
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl (fun j _ => congrArg (c j • ·) (h (f j) (hf j)))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PureFunctionExt.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PureFunctionExt.CM.Sesquilinear

/-! Sesquilinear forms on actual finite Schwartz functions are determined
by pairs of restricted pure tests. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem semilinear_ext (A B : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ⋆[ℂ] ℂ)
    (h : ∀ (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
      (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v),
      A (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf)) =
        B (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf))) : A = B := by
  apply LinearMap.ext
  intro φ
  obtain ⟨t, rfl⟩ := TensorRepresentatives.CM.evaluation_surjective F N φ
  obtain ⟨n, c, f, hf, rfl⟩ := RestrictedTensorExpansion.CM.expansion (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) t
  simp only [map_sum, map_smul, map_smulₛₗ]
  exact Finset.sum_congr rfl (fun j _ => congrArg (star (c j) • ·) (h (f j) (hf j)))

theorem ext
    (A B : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ⋆[ℂ] ℂ)
    (h : ∀ (f k : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
      (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)
      (hk : ∀ᶠ v in cofinite, k v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v),
      A (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf))
        (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) k hk)) =
      B (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf))
        (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) k hk))) : A = B :=
  CM.ext F N A B
    (fun f hf => semilinear_ext F N _ _ (fun k hk => h f k hf hk))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PureFunctionExt.CM.Sesquilinear

end

end OAI
