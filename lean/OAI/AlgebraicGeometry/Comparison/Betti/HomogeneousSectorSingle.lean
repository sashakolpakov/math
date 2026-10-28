import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorNew
import OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousLaurent

/-! # Homogeneous Sector Single -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousSectorSingle.Dolbeault

noncomputable section

section

/-! The homogeneous sector equivalence commutes with actual section restriction. -/

open _root_.TopologicalSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The existing additive structure, shared by restriction declarations. -/
abbrev restrictionSectionAddCommMonoid (s : Finset ι) (d : ℤ) :
    AddCommMonoid (HomogeneousLaurent.Dolbeault.homogeneousLaurentSectionSpace s d) :=
  Submodule.addCommMonoid (HomogeneousLaurent.Dolbeault.laurentHomogeneousSections s d)

/-- The existing additive structure on homogeneous sector families. -/
abbrev restrictionSectorAddCommMonoid (s : Finset ι) (d : ℤ) :
    AddCommMonoid (HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorSpace s d) :=
  Submodule.addCommMonoid (HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies s d)

attribute [local instance] restrictionSectionAddCommMonoid restrictionSectorAddCommMonoid

/-- The existing complex module structure on homogeneous sections. -/
abbrev restrictionSectionModule (s : Finset ι) (d : ℤ) :
    Module ℂ (HomogeneousLaurent.Dolbeault.homogeneousLaurentSectionSpace s d) :=
  Submodule.module (HomogeneousLaurent.Dolbeault.laurentHomogeneousSections s d)

/-- The existing complex module structure on homogeneous sector families. -/
abbrev restrictionSectorModule (s : Finset ι) (d : ℤ) :
    Module ℂ (HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorSpace s d) :=
  Submodule.module (HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies s d)

attribute [local instance] restrictionSectionModule restrictionSectorModule

/-- The original source and target of homogeneous section restriction. -/
abbrev laurentHomogeneousSectionRestrictionType (s t : Finset ι) (d : ℤ) :=
  HomogeneousLaurent.Dolbeault.homogeneousLaurentSectionSpace s d →ₗ[ℂ] HomogeneousLaurent.Dolbeault.homogeneousLaurentSectionSpace t d

/-- The original source and target of homogeneous family inclusion. -/
abbrev laurentHomogeneousFamilyInclusionType (s t : Finset ι) (d : ℤ) :=
  HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorSpace s d →ₗ[ℂ] HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorSpace t d

def laurentHomogeneousSectionRestrict {s t : Finset ι} (hst : s ⊆ t) (d : ℤ) :
    laurentHomogeneousSectionRestrictionType s t d where
  toFun f := ⟨Holomorphic.Restrictions.holomorphicFunctionRestrict (Laurent.SectorTo.Dolbeault.laurentCoordinateDomain_antitone hst) f.val, by
    intro c hc x
    exact f.property c hc ⟨x.val, Laurent.SectorTo.Dolbeault.laurentCoordinateDomain_antitone hst x.property⟩⟩
  map_add' f g := Subtype.ext ((Holomorphic.Restrictions.holomorphicFunctionRestrict
    (Laurent.SectorTo.Dolbeault.laurentCoordinateDomain_antitone hst)).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((Holomorphic.Restrictions.holomorphicFunctionRestrict
    (Laurent.SectorTo.Dolbeault.laurentCoordinateDomain_antitone hst)).toLinearMap.map_smul c f.val)

def laurentHomogeneousFamilyInclusion {s t : Finset ι} (hst : s ⊆ t) (d : ℤ) :
    laurentHomogeneousFamilyInclusionType s t d where
  toFun A := ⟨Laurent.SectorNew.Dolbeault.laurentSectorFamilyInclusion hst A.val, A.property⟩
  map_add' A B := Subtype.ext ((Laurent.SectorNew.Dolbeault.laurentSectorFamilyInclusion hst).map_add A.val B.val)
  map_smul' c A := Subtype.ext ((Laurent.SectorNew.Dolbeault.laurentSectorFamilyInclusion hst).map_smul c A.val)

/-- The original compatibility identity, with its complete expression shared. -/
abbrev homogeneousLaurentRestrictionIdentity {s t : Finset ι} (hst : s ⊆ t) (d : ℤ)
    (f : HomogeneousLaurent.Dolbeault.homogeneousLaurentSectionSpace s d) : Prop :=
    HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorEquiv t d (laurentHomogeneousSectionRestrict hst d f) =
      laurentHomogeneousFamilyInclusion hst d (HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorEquiv s d f)

theorem homogeneousLaurentSectorEquiv_restrict {s t : Finset ι} (hst : s ⊆ t) (d : ℤ)
    (f : HomogeneousLaurent.Dolbeault.homogeneousLaurentSectionSpace s d) :
    homogeneousLaurentRestrictionIdentity hst d f :=
  Subtype.ext (Laurent.SectorNew.Dolbeault.laurentSectorEquiv_restrict hst f.val)

end

section

/-! Each Laurent sign sector has its own fixed homogeneous coefficient space. -/

open _root_.TopologicalSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def homogeneousSectorCoefficients (J : Finset ι) (d : ℤ) :
    Submodule ℂ (Holomorphic.FunctionPure.holomorphicFunctions (⊤ : Opens (ι → ℂ))) where
  carrier := {a | a ∈ Laurent.SectorTo.Dolbeault.laurentSectorCoefficients J ∧
    ∀ c : ℂ, c ≠ 0 → ∀ x : ι → ℂ,
      Laurent.SectorSum.Dolbeault.laurentEntireFunction a (Laurent.FiniteUniqueness.Dolbeault.laurentSectorScale c J x) = c ^ d * Laurent.SectorSum.Dolbeault.laurentEntireFunction a x}
  zero_mem' := ⟨(Laurent.SectorTo.Dolbeault.laurentSectorCoefficients J).zero_mem, fun c _ _ => (mul_zero (c ^ d)).symm⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨(Laurent.SectorTo.Dolbeault.laurentSectorCoefficients J).add_mem ha.1 hb.1, ?_⟩
    intro c hc x
    change Laurent.SectorSum.Dolbeault.laurentEntireFunction a _ + Laurent.SectorSum.Dolbeault.laurentEntireFunction b _ =
      c ^ d * (Laurent.SectorSum.Dolbeault.laurentEntireFunction a x + Laurent.SectorSum.Dolbeault.laurentEntireFunction b x)
    rw [ha.2 c hc x, hb.2 c hc x, mul_add]
  smul_mem' := by
    intro r a ha
    refine ⟨(Laurent.SectorTo.Dolbeault.laurentSectorCoefficients J).smul_mem r ha.1, ?_⟩
    intro c hc x
    change r * Laurent.SectorSum.Dolbeault.laurentEntireFunction a _ = c ^ d * (r * Laurent.SectorSum.Dolbeault.laurentEntireFunction a x)
    rw [ha.2 c hc x]
    ring

def homogeneousSectorCoefficientMap (s : Finset ι) (d : ℤ) (J : Finset ι) :
    HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies s d →ₗ[ℂ] homogeneousSectorCoefficients J d where
  toFun A := ⟨A.val.val J, A.val.property.1 J, A.property J⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem homogeneousSectorCoefficientMap_inclusion {s t : Finset ι} (hst : s ⊆ t)
    (d : ℤ) (J : Finset ι) (A : HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies s d) :
    homogeneousSectorCoefficientMap t d J (laurentHomogeneousFamilyInclusion hst d A) =
      homogeneousSectorCoefficientMap s d J A := rfl

theorem homogeneousSectorCoefficientMap_zero_of_not_subset (s : Finset ι) (d : ℤ) (J : Finset ι)
    (hJ : ¬J ⊆ s) (A : HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies s d) :
    homogeneousSectorCoefficientMap s d J A = 0 :=
  Subtype.ext (A.val.property.2 J hJ)

theorem homogeneousSectorFamily_ext (s : Finset ι) (d : ℤ)
    (A B : HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies s d)
    (h : ∀ J, homogeneousSectorCoefficientMap s d J A = homogeneousSectorCoefficientMap s d J B) : A = B := by
  apply Subtype.ext
  apply Subtype.ext
  funext J
  exact congrArg Subtype.val (h J)

end

section

/-! A single normalized coefficient gives its actual homogeneous Laurent sector and no others. -/

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def homogeneousSingleSectorFamily (s J : Finset ι) (hJ : J ⊆ s) (d : ℤ)
    (a : homogeneousSectorCoefficients J d) : HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies s d := by
  let A := fun K : Finset ι => if K = J then a.val else 0
  refine ⟨⟨A, ?_, ?_⟩, ?_⟩
  · intro K
    by_cases h : K = J
    · subst K
      simpa only [A, ite_eq_left rfl] using a.property.1
    · simpa only [A, ite_eq_right h] using (Laurent.SectorTo.Dolbeault.laurentSectorCoefficients K).zero_mem
  · intro K hK
    have h : K ≠ J := fun he => hK (he ▸ hJ)
    exact ite_eq_right h
  · intro K c hc x
    by_cases h : K = J
    · subst K
      simpa only [A, ite_eq_left rfl] using a.property.2 c hc x
    · change Laurent.SectorSum.Dolbeault.laurentEntireFunction (A K) _ = c ^ d * Laurent.SectorSum.Dolbeault.laurentEntireFunction (A K) x
      rw [show A K = 0 from ite_eq_right h]
      exact (mul_zero (c ^ d)).symm

theorem homogeneousSingleSectorFamily_coefficient (s J : Finset ι) (hJ : J ⊆ s) (d : ℤ)
    (a : homogeneousSectorCoefficients J d) :
    homogeneousSectorCoefficientMap s d J (homogeneousSingleSectorFamily s J hJ d a) = a := by
  apply Subtype.ext
  change (if J = J then a.val else 0) = a.val
  exact ite_eq_left rfl

theorem homogeneousSingleSectorFamily_coefficient_ne (s J K : Finset ι) (hJ : J ⊆ s) (d : ℤ)
    (a : homogeneousSectorCoefficients J d) (hK : K ≠ J) :
    homogeneousSectorCoefficientMap s d K (homogeneousSingleSectorFamily s J hJ d a) = 0 := by
  apply Subtype.ext
  change (if K = J then a.val else 0) = 0
  exact ite_eq_right hK

theorem homogeneousSingleSectorFamily_assembly (s J : Finset ι) (hJ : J ⊆ s) (d : ℤ)
    (a : homogeneousSectorCoefficients J d) (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) :
    ((HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorEquiv s d).symm (homogeneousSingleSectorFamily s J hJ d a)).val.val x =
      Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates J x.val) := by
  change (∑ K ∈ s.powerset, Laurent.SectorSum.Dolbeault.laurentEntireFunction (if K = J then a.val else 0)
    (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates K x.val)) = _
  rw [Finset.sum_eq_single J]
  · rw [ite_eq_left rfl]
  · intro K _ hK
    rw [ite_eq_right hK]
    rfl
  · intro h
    exact (h (Finset.mem_powerset.mpr hJ)).elim

end

/-! Values determine the actual Laurent sector of a homogeneous section. -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem homogeneousLaurentSectorEquiv_of_single_values (s J : Finset ι) (hJ : J ⊆ s) (d : ℤ)
    (a : homogeneousSectorCoefficients J d) (f : HomogeneousLaurent.Dolbeault.laurentHomogeneousSections s d)
    (hf : ∀ x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s, f.val.val x =
      Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates J x.val)) :
    HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorEquiv s d f = homogeneousSingleSectorFamily s J hJ d a := by
  have he : f = (HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorEquiv s d).symm (homogeneousSingleSectorFamily s J hJ d a) := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact (hf x).trans (homogeneousSingleSectorFamily_assembly s J hJ d a x).symm
  exact (congrArg (HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorEquiv s d) he).trans
    ((HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorEquiv s d).apply_symm_apply _)

theorem homogeneousSectorCoefficient_of_single_values (s J : Finset ι) (hJ : J ⊆ s) (d : ℤ)
    (a : homogeneousSectorCoefficients J d) (f : HomogeneousLaurent.Dolbeault.laurentHomogeneousSections s d)
    (hf : ∀ x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s, f.val.val x =
      Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates J x.val)) :
    homogeneousSectorCoefficientMap s d J (HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorEquiv s d f) = a :=
  (congrArg (homogeneousSectorCoefficientMap s d J)
    (homogeneousLaurentSectorEquiv_of_single_values s J hJ d a f hf)).trans
      (homogeneousSingleSectorFamily_coefficient s J hJ d a)

end

end OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousSectorSingle.Dolbeault
