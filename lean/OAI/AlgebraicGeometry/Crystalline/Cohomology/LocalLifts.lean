import OAI.AlgebraicGeometry.Crystalline.Cohomology.FunctionsSeparation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Local Lifts -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalLifts.CrystallineLocalLifts

noncomputable section

/-!
# Finite principal local lifts for epimorphisms of native sheaves

Every native covering sieve contains a finite unit-ideal principal cover.
Consequently each section of the target of an epimorphism of native
Witt-module sheaves lifts on such an actual finite principal cover.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k

theorem finite_refinement {Q : Site.Object p k X} (S : Sieve Q) (hS : S ∈ J Q) :
    ∃ t : Finset Q.thickening.ring, Ideal.span (t : Set Q.thickening.ring) = ⊤ ∧
      ∀ s ∈ t, S (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s) := by
  have hspan := FunctionsSeparation.CrystallineFunctionsSeparation.coefficients_span p k X S hS
  have h1 : (1 : Q.thickening.ring) ∈ Ideal.span (FunctionsSeparation.CrystallineFunctionsSeparation.coefficients p k X S) := by
    rw [hspan]
    trivial
  obtain ⟨t, ht, h1t⟩ := Submodule.mem_span_finite_of_mem_span h1
  exact ⟨t, (Ideal.eq_top_iff_one _).mpr h1t, fun s hs => ht hs⟩

theorem exists_principal_lifts {F G : Sheaf J V} (φ : F ⟶ G) [Epi φ]
    (Q : Site.Object p k X) (x : G.obj.obj (op Q)) :
    ∃ t : Finset Q.thickening.ring, Ideal.span (t : Set Q.thickening.ring) = ⊤ ∧
      ∀ s : t, ∃ y : F.obj.obj (op (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q s.val)),
        φ.hom.app _ y = G.obj.map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s.val).op x := by
  have : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi' V φ).mpr inferInstance
  obtain ⟨t, ht, hmem⟩ := finite_refinement p k X (Presheaf.imageSieve φ.hom x)
    (Presheaf.imageSieve_mem J φ.hom x)
  exact ⟨t, ht, fun s => hmem s.val s.property⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalLifts.CrystallineLocalLifts
