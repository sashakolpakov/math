import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BasisIsomorphisms
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Basis Gluing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BasisGluing

noncomputable section

/-! Compatible maps on affine neighborhoods glue once compatibility
is checked on principal subopens. Common principal neighborhoods
compare arbitrary overlaps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}} (M N : X.Modules) (P : X.Opens → Prop)
  (φ : ∀ (U : X.Opens) (_ : IsAffineOpen U), P U → Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U))
  (hstable : ∀ (U : X.Opens) (_ : IsAffineOpen U), P U → ∀ r : Γ(X, U), P (X.basicOpen r))
  (hφ : ∀ (U : X.Opens) (hU : IsAffineOpen U) (hP : P U) (r : Γ(X, U)) (s : Γ(M, U)),
    φ (X.basicOpen r) (hU.basicOpen r) (hstable U hU hP r)
        (M.presheaf.map (homOfLE (X.basicOpen_le r)).op s) =
      N.presheaf.map (homOfLE (X.basicOpen_le r)).op (φ U hU hP s))

theorem restriction_condition_congr (U V W : X.Opens)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hPV : P V) (hPW : P W)
    (hVU : V ≤ U) (hWU : W ≤ U) (he : V = W) (s : Γ(M, U)) (t : Γ(N, U)) :
    (φ V hV hPV (M.presheaf.map (homOfLE hVU).op s) =
      N.presheaf.map (homOfLE hVU).op t) ↔
    (φ W hW hPW (M.presheaf.map (homOfLE hWU).op s) =
      N.presheaf.map (homOfLE hWU).op t) := by
  subst W
  rfl

include hφ in
theorem naturality (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hPU : P U) (hPV : P V) (hVU : V ≤ U) (s : Γ(M, U)) :
    φ V hV hPV (M.presheaf.map (homOfLE hVU).op s) =
      N.presheaf.map (homOfLE hVU).op (φ U hU hPU s) := by
  apply N.isSheaf.section_ext
  intro x hx
  obtain ⟨r, t, he, hxr⟩ := exists_basicOpen_le_affine_inter hV hU x ⟨hx, hVU hx⟩
  refine ⟨X.basicOpen r, X.basicOpen_le r, hxr, ?_⟩
  have hW : X.basicOpen r ≤ U := (X.basicOpen_le r).trans hVU
  have hu :
      φ (X.basicOpen r) (hV.basicOpen r) (hstable V hV hPV r)
          (M.presheaf.map (homOfLE hW).op s) =
        N.presheaf.map (homOfLE hW).op (φ U hU hPU s) := by
    exact (restriction_condition_congr M N P φ U (X.basicOpen t) (X.basicOpen r)
      (hU.basicOpen t) (hV.basicOpen r) (hstable U hU hPU t) (hstable V hV hPV r)
      (X.basicOpen_le t) hW he.symm s (φ U hU hPU s)).mp (hφ U hU hPU t s)
  rw [← hφ V hV hPV r, ← M.presheaf.map_comp_apply, ← N.presheaf.map_comp_apply]
  exact hu

abbrev Index := {U : X.Opens // IsAffineOpen U ∧ P U}

def opens : Index P → X.Opens := Subtype.val

def basisMap : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapBasisExtension.ModuleBasisMap (opens P) M N where
  app i := φ i.val i.property.1 i.property.2
  naturality i j h s := BasisGluing.naturality M N P φ hstable hφ j.val i.val j.property.1 i.property.1
    j.property.2 i.property.2 h s

variable (hcover : ∀ (V : X.Opens) (x : X), x ∈ V →
  ∃ (U : X.Opens), IsAffineOpen U ∧ P U ∧ x ∈ U ∧ U ≤ V)

include hcover in
theorem isBasis : Opens.IsBasis (Set.range (opens P)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨U, hU, hP, hxU, hUV⟩ := hcover V x hx
  exact ⟨U, ⟨⟨U, hU, hP⟩, rfl⟩, hxU, hUV⟩

def iso (hbij : ∀ (U : X.Opens) (hU : IsAffineOpen U) (hP : P U),
    Function.Bijective (φ U hU hP)) : M ≅ N :=
  (basisMap M N P φ hstable hφ).extendIso (opens P) (isBasis P hcover)
    (fun i => hbij i.val i.property.1 i.property.2)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BasisGluing
