import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorSum
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.LaurentSectors
import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.FiniteUniqueness

/-! # Sector New -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorNew.Dolbeault

noncomputable section

section

/-! The actual section assembly map is bijective. -/

open _root_.TopologicalSpace Set
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem laurentSectorAssembly_injective (s : Finset ι) :
    Function.Injective (SectorSum.Dolbeault.laurentSectorAssemblyMap s) := by
  intro A B h
  have he : ∀ J ∈ s.powerset, SectorSum.Dolbeault.laurentEntireFunction (A.val J) = SectorSum.Dolbeault.laurentEntireFunction (B.val J) := by
    apply FiniteUniqueness.Dolbeault.finiteLaurentSectors_unique s
      (fun J => SectorSum.Dolbeault.laurentEntireFunction (A.val J)) (fun J => SectorSum.Dolbeault.laurentEntireFunction (B.val J))
      (fun J _ => SectorSum.Dolbeault.laurentEntireFunction_differentiable (A.val J))
      (fun J _ => SectorSum.Dolbeault.laurentEntireFunction_differentiable (B.val J))
    · intro J _ j hj x hx
      exact A.property.1 J j hj ⟨x, trivial⟩ hx
    · intro J _ j hj x hx
      exact B.property.1 J j hj ⟨x, trivial⟩ hx
    · intro x hx
      exact congrArg (fun f : Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s) => f.val ⟨x, hx⟩) h
  apply Subtype.ext
  funext J
  by_cases hJs : J ⊆ s
  · apply Subtype.ext
    funext x
    exact congrFun (he J (Finset.mem_powerset.mpr hJs)) x.val
  · exact (A.property.2 J hJs).trans (B.property.2 J hJs).symm

theorem laurentSectorAssembly_surjective (s : Finset ι) :
    Function.Surjective (SectorSum.Dolbeault.laurentSectorAssemblyMap s) := by
  intro f
  obtain ⟨A, hA, hAe⟩ := Finite.LaurentSectors.Dolbeault.exists_finiteLaurentSectors s ∅ (by simp)
    (FiberVanishing.Dolbeault.holomorphicFunctionExtension _ f) (FiberVanishing.Dolbeault.holomorphicFunctionExtension_differentiable _ f)
    (by simp)
  let B : Finset ι → Holomorphic.FunctionPure.holomorphicFunctions (⊤ : Opens (ι → ℂ)) := fun J =>
    if hJ : J ⊆ s then PolynomialHolomorphicSections.AnalyticLocal.functionSectionOfDifferentiable ⊤ (A J)
      ((hA J (Finset.mem_powerset.mpr hJ)).1.differentiableOn) else 0
  have hB : B ∈ SectorSum.Dolbeault.laurentSectorSectionFamilies s := by
    constructor
    · intro J
      by_cases hJs : J ⊆ s
      · intro j hj x hx
        simp only [B, dite_eq_left hJs]
        exact (hA J (Finset.mem_powerset.mpr hJs)).2 j (Finset.mem_union_left _ hj) x.val hx
      · simpa only [B, dite_eq_right hJs] using (SectorTo.Dolbeault.laurentSectorCoefficients J).zero_mem
    · intro J hJ
      simp only [B, dite_eq_right hJ]
  refine ⟨⟨B, hB⟩, ?_⟩
  apply Subtype.ext
  funext x
  calc
    (SectorSum.Dolbeault.laurentSectorAssemblyMap s ⟨B, hB⟩).val x =
        ∑ J ∈ s.powerset, A J (SectorTo.Dolbeault.laurentInverseCoordinates J x.val) := by
      change (∑ J ∈ s.powerset, (B J).val ⟨SectorTo.Dolbeault.laurentInverseCoordinates J x.val, trivial⟩) = _
      apply Finset.sum_congr rfl
      intro J hJ
      simp only [B, dite_eq_left (Finset.mem_powerset.mp hJ)]
      rfl
    _ = FiberVanishing.Dolbeault.holomorphicFunctionExtension _ f x.val := hAe x.val x.property
    _ = f.val x := Holomorphic.CoefficientMem.openCoefficientExtension_apply _ f.val x

end

section

/-! A linear equivalence between actual holomorphic sections and finite sectors. -/

open _root_.TopologicalSpace
open scoped BigOperators _root_.Manifold ContDiff

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def laurentSectorEquiv (s : Finset ι) :
    Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s) ≃ₗ[ℂ] SectorSum.Dolbeault.laurentSectorSectionFamilies s :=
  (LinearEquiv.ofBijective (SectorSum.Dolbeault.laurentSectorAssemblyMap s)
    ⟨laurentSectorAssembly_injective s, laurentSectorAssembly_surjective s⟩).symm

theorem laurentSectorAssembly_equiv (s : Finset ι)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s)) :
    SectorSum.Dolbeault.laurentSectorAssemblyMap s (laurentSectorEquiv s f) = f :=
  (laurentSectorEquiv s).symm_apply_apply f

theorem laurentSectorEquiv_assembly (s : Finset ι) (A : SectorSum.Dolbeault.laurentSectorSectionFamilies s) :
    laurentSectorEquiv s (SectorSum.Dolbeault.laurentSectorAssemblyMap s A) = A :=
  (laurentSectorEquiv s).apply_symm_apply A

theorem laurentSectorEquiv_reconstruct (s : Finset ι)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s)) (x : SectorTo.Dolbeault.laurentCoordinateDomain s) :
    ∑ J ∈ s.powerset, ((laurentSectorEquiv s f).val J).val
      ⟨SectorTo.Dolbeault.laurentInverseCoordinates J x.val, trivial⟩ = f.val x := by
  exact congrArg (fun g : Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s) => g.val x)
    (laurentSectorAssembly_equiv s f)

def nativeLaurentSectorEquiv (s : Finset ι) :
    C^∞⟮𝓘(ℂ, ι → ℂ), SectorTo.Dolbeault.laurentCoordinateDomain s; 𝓘(ℂ), ℂ⟯ ≃ₗ[ℂ]
      SectorSum.Dolbeault.laurentSectorSectionFamilies s :=
  (Holomorphic.StandardFunctionSheaf.AnalyticLocal.holomorphicFunctionContMDiffEquiv (ι → ℂ)
    (SectorTo.Dolbeault.laurentCoordinateDomain s)).symm.toLinearEquiv.trans (laurentSectorEquiv s)

end

/-! Laurent sector coordinates commute with the original holomorphic restriction. -/

open _root_.TopologicalSpace
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def laurentSectorFamilyInclusion {s t : Finset ι} (hst : s ⊆ t) :
    SectorSum.Dolbeault.laurentSectorSectionFamilies s →ₗ[ℂ] SectorSum.Dolbeault.laurentSectorSectionFamilies t where
  toFun A := ⟨A.val, A.property.1, fun J hJ => A.property.2 J (fun hJs => hJ (hJs.trans hst))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem laurentSectorAssembly_restrict {s t : Finset ι} (hst : s ⊆ t)
    (A : SectorSum.Dolbeault.laurentSectorSectionFamilies s) :
    Holomorphic.Restrictions.holomorphicFunctionRestrict (SectorTo.Dolbeault.laurentCoordinateDomain_antitone hst) (SectorSum.Dolbeault.laurentSectorAssemblyMap s A) =
      SectorSum.Dolbeault.laurentSectorAssemblyMap t (laurentSectorFamilyInclusion hst A) := by
  apply Subtype.ext
  funext x
  change (∑ J ∈ s.powerset, (A.val J).val ⟨SectorTo.Dolbeault.laurentInverseCoordinates J x.val, trivial⟩) =
    ∑ J ∈ t.powerset, (A.val J).val ⟨SectorTo.Dolbeault.laurentInverseCoordinates J x.val, trivial⟩
  apply Finset.sum_subset
  · intro J hJ
    exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hJ).trans hst)
  · intro J _ hJ
    have hz : A.val J = 0 := A.property.2 J (fun h => hJ (Finset.mem_powerset.mpr h))
    rw [hz]
    rfl

theorem laurentSectorEquiv_restrict {s t : Finset ι} (hst : s ⊆ t)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s)) :
    laurentSectorEquiv t (Holomorphic.Restrictions.holomorphicFunctionRestrict (SectorTo.Dolbeault.laurentCoordinateDomain_antitone hst) f) =
      laurentSectorFamilyInclusion hst (laurentSectorEquiv s f) := by
  apply laurentSectorAssembly_injective t
  rw [laurentSectorAssembly_equiv, ← laurentSectorAssembly_restrict, laurentSectorAssembly_equiv]

theorem laurentSectorEquiv_restrict_new_zero {s t : Finset ι} (hst : s ⊆ t)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s)) (J : Finset ι) (hJ : ¬J ⊆ s) :
    (laurentSectorEquiv t (Holomorphic.Restrictions.holomorphicFunctionRestrict (SectorTo.Dolbeault.laurentCoordinateDomain_antitone hst) f)).val J = 0 := by
  rw [laurentSectorEquiv_restrict hst f]
  exact (laurentSectorEquiv s f).property.2 J hJ

end

end OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorNew.Dolbeault
