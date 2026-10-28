import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Topology
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Functions Separation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FunctionsSeparation.CrystallineFunctionsSeparation

noncomputable section

/-! # Separation of actual crystalline ambient functions on native covers -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

def values : (Site.Object p k X)ᵒᵖ ⥤ Type u :=
  Site.functions p k X ⋙ forget (ModuleCat.{u} (WittVector p k))

def coefficients {Q : Site.Object p k X} (S : Sieve Q) : Set Q.thickening.ring :=
  {s | S (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s)}

theorem coefficients_span {Q : Site.Object p k X} (S : Sieve Q)
    (hS : S ∈ Site.topology p k X Q) : Ideal.span (coefficients p k X S) = ⊤ := by
  have hlocal := (CrystallinePrincipal.Topology.CrystallinePrincipalTopology.covering_iff p k X S).mp hS
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
  apply top_le_iff.mp
  intro x _
  obtain ⟨s, hs, hmem⟩ := hlocal x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, TopologicalSpace.Opens.mem_iSup.mpr ⟨hmem, hs⟩⟩

theorem ext {Q : Site.Object p k X} (S : Sieve Q)
    (hS : S ∈ Site.topology p k X Q) (x y : Q.thickening.ring)
    (h : ∀ {P : Site.Object p k X} (f : P ⟶ Q), S f → f.ambientMap x = f.ambientMap y) : x = y := by
  apply Localization.algebraMap_injective_of_span_eq_top (coefficients p k X S) (coefficients_span p k X S hS)
  funext s
  exact h (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s.val) s.property

theorem separated {Q : Site.Object p k X} (S : Sieve Q)
    (hS : S ∈ Site.topology p k X Q) : Presieve.IsSeparatedFor (values p k X) S.arrows := by
  intro z x y hx hy
  apply ext p k X S hS x y
  intro P f hf
  exact (hx f hf).trans (hy f hf).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FunctionsSeparation.CrystallineFunctionsSeparation
