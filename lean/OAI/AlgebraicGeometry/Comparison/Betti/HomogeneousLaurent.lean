import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorNew
import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.FiniteUniqueness

/-! # Homogeneous Laurent -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousLaurent.Dolbeault

noncomputable section

section

/-! Homogeneous holomorphic functions and their independently defined sector spaces. -/

open _root_.TopologicalSpace Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def laurentScaledPoint (s : Finset ι) (c : ℂ) (hc : c ≠ 0)
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s :=
  ⟨Laurent.FiniteUniqueness.Dolbeault.laurentUniformScale c x.val, Laurent.FiniteUniqueness.Dolbeault.laurentUniformScale_mem s c hc x.val x.property⟩

def laurentHomogeneousSections (s : Finset ι) (d : ℤ) :
    Submodule ℂ (Holomorphic.FunctionPure.holomorphicFunctions (Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s)) where
  carrier := {f | ∀ c : ℂ, ∀ hc : c ≠ 0, ∀ x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s,
    f.val (laurentScaledPoint s c hc x) = c ^ d * f.val x}
  zero_mem' := by
    intro c hc x
    exact (mul_zero (c ^ d)).symm
  add_mem' := by
    intro f g hf hg c hc x
    change f.val _ + g.val _ = c ^ d * (f.val x + g.val x)
    rw [hf c hc x, hg c hc x, mul_add]
  smul_mem' := by
    intro a f hf c hc x
    change a * f.val _ = c ^ d * (a * f.val x)
    rw [hf c hc x]
    ring

def laurentHomogeneousSectorFamilies (s : Finset ι) (d : ℤ) :
    Submodule ℂ (Laurent.SectorSum.Dolbeault.laurentSectorSectionFamilies s) where
  carrier := {A | ∀ J : Finset ι, ∀ c : ℂ, c ≠ 0 → ∀ x : ι → ℂ,
    Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J) (Laurent.FiniteUniqueness.Dolbeault.laurentSectorScale c J x) =
      c ^ d * Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J) x}
  zero_mem' := by
    intro J c hc x
    exact (mul_zero (c ^ d)).symm
  add_mem' := by
    intro A B hA hB J c hc x
    change Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J) _ + Laurent.SectorSum.Dolbeault.laurentEntireFunction (B.val J) _ =
      c ^ d * (Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J) x + Laurent.SectorSum.Dolbeault.laurentEntireFunction (B.val J) x)
    rw [hA J c hc x, hB J c hc x, mul_add]
  smul_mem' := by
    intro a A hA J c hc x
    change a * Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J) _ = c ^ d * (a * Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J) x)
    rw [hA J c hc x]
    ring

end

/-! Homogeneity is preserved in both directions by the actual sector equivalence. -/

open _root_.TopologicalSpace Set
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- These transparent names retain the original spaces and homogeneity conditions. -/
abbrev homogeneousLaurentFunctionSpace (s : Finset ι) : Type :=
  Holomorphic.FunctionPure.holomorphicFunctions (Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s)

abbrev homogeneousLaurentFamilySpace (s : Finset ι) : Type :=
  Laurent.SectorSum.Dolbeault.laurentSectorSectionFamilies s

abbrev homogeneousLaurentSectionCondition (s : Finset ι) (d : ℤ)
    (f : homogeneousLaurentFunctionSpace s) : Prop :=
  f ∈ laurentHomogeneousSections s d

abbrev homogeneousLaurentFamilyCondition (s : Finset ι) (d : ℤ)
    (A : homogeneousLaurentFamilySpace s) : Prop :=
  A ∈ laurentHomogeneousSectorFamilies s d

abbrev homogeneousLaurentSectorImageCondition (s : Finset ι) (d : ℤ)
    (f : homogeneousLaurentFunctionSpace s) : Prop :=
  Laurent.SectorNew.Dolbeault.laurentSectorEquiv s f ∈ laurentHomogeneousSectorFamilies s d

abbrev homogeneousLaurentAssemblyImageCondition (s : Finset ι) (d : ℤ)
    (A : homogeneousLaurentFamilySpace s) : Prop :=
  Laurent.SectorSum.Dolbeault.laurentSectorAssemblyMap s A ∈ laurentHomogeneousSections s d

abbrev homogeneousLaurentSectionSpace (s : Finset ι) (d : ℤ) : Type :=
  laurentHomogeneousSections s d

abbrev homogeneousLaurentSectorSpace (s : Finset ι) (d : ℤ) : Type :=
  laurentHomogeneousSectorFamilies s d

abbrev homogeneousLaurentSectorEquivType (s : Finset ι) (d : ℤ) : Type :=
  homogeneousLaurentSectionSpace s d ≃ₗ[ℂ] homogeneousLaurentSectorSpace s d

theorem laurentSectorEquiv_homogeneous (s : Finset ι) (d : ℤ)
    (f : homogeneousLaurentFunctionSpace s)
    (hf : homogeneousLaurentSectionCondition s d f) :
    homogeneousLaurentSectorImageCondition s d f := by
  let A := Laurent.SectorNew.Dolbeault.laurentSectorEquiv s f
  have hrec (x : ι → ℂ) (hx : x ∈ Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) :
      Laurent.SectorSum.Dolbeault.laurentSectorSum s (fun J => Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J)) x = f.val ⟨x, hx⟩ :=
    Laurent.SectorNew.Dolbeault.laurentSectorEquiv_reconstruct s f ⟨x, hx⟩
  intro J c hc x
  by_cases hJs : J ⊆ s
  · have hh : ∀ y ∈ Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s,
        Laurent.SectorSum.Dolbeault.laurentSectorSum s (fun J => Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J)) (Laurent.FiniteUniqueness.Dolbeault.laurentUniformScale c y) =
          c ^ d * Laurent.SectorSum.Dolbeault.laurentSectorSum s (fun J => Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J)) y := by
      intro y hy
      rw [hrec _ (Laurent.FiniteUniqueness.Dolbeault.laurentUniformScale_mem s c hc y hy), hrec y hy]
      exact hf c hc ⟨y, hy⟩
    exact Laurent.FiniteUniqueness.Dolbeault.finiteLaurentSectors_scaling s (fun J => Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J))
      (fun J _ => Laurent.SectorSum.Dolbeault.laurentEntireFunction_differentiable (A.val J))
      (fun J _ j hj y hy => A.property.1 J j hj ⟨y, trivial⟩ hy)
      c (c ^ d) hh J (Finset.mem_powerset.mpr hJs) x
  · change Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J) _ = c ^ d * Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J) x
    rw [A.property.2 J hJs]
    exact (mul_zero (c ^ d)).symm

theorem laurentSectorAssembly_homogeneous (s : Finset ι) (d : ℤ)
    (A : homogeneousLaurentFamilySpace s)
    (hA : homogeneousLaurentFamilyCondition s d A) :
    homogeneousLaurentAssemblyImageCondition s d A := by
  intro c hc x
  change Laurent.SectorSum.Dolbeault.laurentSectorSum s (fun J => Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J)) (Laurent.FiniteUniqueness.Dolbeault.laurentUniformScale c x.val) =
    c ^ d * Laurent.SectorSum.Dolbeault.laurentSectorSum s (fun J => Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J)) x.val
  calc
    Laurent.SectorSum.Dolbeault.laurentSectorSum s (fun J => Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J)) (Laurent.FiniteUniqueness.Dolbeault.laurentUniformScale c x.val) =
        ∑ J ∈ s.powerset, c ^ d * Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J) (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates J x.val) := by
      apply Finset.sum_congr rfl
      intro J _
      rw [Laurent.FiniteUniqueness.Dolbeault.laurentInverseCoordinates_scale]
      exact hA J c hc _
    _ = c ^ d * Laurent.SectorSum.Dolbeault.laurentSectorSum s (fun J => Laurent.SectorSum.Dolbeault.laurentEntireFunction (A.val J)) x.val :=
      (Finset.mul_sum s.powerset _ (c ^ d)).symm

def homogeneousLaurentSectorEquiv (s : Finset ι) (d : ℤ) :
    homogeneousLaurentSectorEquivType s d where
  toFun f := ⟨Laurent.SectorNew.Dolbeault.laurentSectorEquiv s f.val, laurentSectorEquiv_homogeneous s d f.val f.property⟩
  invFun A := ⟨Laurent.SectorSum.Dolbeault.laurentSectorAssemblyMap s A.val, laurentSectorAssembly_homogeneous s d A.val A.property⟩
  map_add' f g := Subtype.ext ((Laurent.SectorNew.Dolbeault.laurentSectorEquiv s).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((Laurent.SectorNew.Dolbeault.laurentSectorEquiv s).map_smul c f.val)
  left_inv f := Subtype.ext (Laurent.SectorNew.Dolbeault.laurentSectorAssembly_equiv s f.val)
  right_inv A := Subtype.ext (Laurent.SectorNew.Dolbeault.laurentSectorEquiv_assembly s A.val)

end

end OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousLaurent.Dolbeault
