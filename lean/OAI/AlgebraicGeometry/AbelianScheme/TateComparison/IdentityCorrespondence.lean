import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELUnitIsomorphism
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ModuliUniqueness
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralBranches
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseTrace

/-! # Identity Correspondence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

section

/-! The zero cocharacter is the geometric identity correspondence. Its
unique branch has a multiplier-one PEL isogeny, so fine moduli uniqueness
identifies its target with its source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

section

def Local.IntegralType.identity (s : ℕ) : Local.IntegralType s :=
  ⟨⟨0, fun _ _ => 0, fun _ _ _ _ => le_rfl⟩, le_rfl, fun _ _ => ⟨le_rfl, le_rfl⟩⟩

@[simp] theorem Local.IntegralType.identity_multiplierNat (s : ℕ) : (Local.IntegralType.identity s).multiplierNat = 0 := rfl
@[simp] theorem Local.IntegralType.identity_exponentNat (s : ℕ) (v : Fin s) (i : Fin 3) :
    (Local.IntegralType.identity s).exponentNat v i = 0 := rfl

end

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (h : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient)

include hg h hIsogenyQuotient in
theorem Data.SphericalPELAlbaneseData.identityBranch_target_eq_source {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K))
    (c : Over.mk b ⟶ (D.correspondence (Local.IntegralType.identity s)).cover) :
    c ≫ (D.correspondence (Local.IntegralType.identity s)).target =
      c ≫ (D.correspondence (Local.IntegralType.identity s)).source := by
  have := FiberLattices.charZero_of_field_spec_map b
  let x := c ≫ (D.correspondence (Local.IntegralType.identity s)).source
  let y := c ≫ (D.correspondence (Local.IntegralType.identity s)).target
  let f : PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) 1 := (D.c46FiberIsogeny hIsogenyQuotient (Local.IntegralType.identity s) x y c rfl rfl).castMultiplier
    (by simp only [Local.IntegralType.identity_multiplierNat, pow_zero])
  let e := f.multiplierOneFamilyIso q D.reference.polarizationType
    (D.fiberPolarizationType h b x) (D.fiberPolarizationType h b y) hg.2.2.2.2
  have : IsReduced (Over.mk b).left := inferInstanceAs (IsReduced (Spec (.of k)))
  exact (D.genericMap_eq_of_familyIso h x y e).symm

include hg hdegree hs h hIsogenyQuotient in
theorem Data.SphericalPELAlbaneseData.identityBranchCount {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b) :
    Nat.card ((D.correspondence (Local.IntegralType.identity s)).Fiber x) = 1 := by
  rw [D.geometricBranchCount hg hdegree hs h b x hIsogenyQuotient]
  simp only [Local.IntegralType.identity_exponentNat, Nat.cast_zero, CentralBranches.rawScalarBlock_card,
    Finset.prod_const_one]

include hg hdegree hs h hIsogenyQuotient in
theorem Data.SphericalPELAlbaneseData.identitySource_isIso : IsIso (D.correspondence (Local.IntegralType.identity s)).source :=
  (D.correspondence (Local.IntegralType.identity s)).source_isIso_of_fiber_card_one
    (fun k _ _ b x => D.identityBranchCount hg hdegree hs h hIsogenyQuotient (k := k) b x)

include hg hdegree hs h hIsogenyQuotient in
theorem Data.SphericalPELAlbaneseData.identity_targetMap_eq_id :
    letI := D.identitySource_isIso hg hdegree hs h hIsogenyQuotient
    inv (D.correspondence (Local.IntegralType.identity s)).source ≫
      (D.correspondence (Local.IntegralType.identity s)).target = 𝟙 D.space := by
  have := D.identitySource_isIso hg hdegree hs h hIsogenyQuotient
  have := D.genericSpace_reduced h
  have : IsProper D.model.space.hom := h.proper
  have : IsSeparated D.space.hom := inferInstanceAs
    (IsSeparated (CategoryTheory.Limits.pullback.snd D.model.space.hom D.generic))
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ b x
  have he := D.identityBranch_target_eq_source hg h hIsogenyQuotient b
    (x ≫ inv (D.correspondence (Local.IntegralType.identity s)).source)
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using he

include hg hdegree hs h hIsogenyQuotient in
theorem Data.SphericalPELAlbaneseData.identity_neighbors {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b) :
    D.neighbors (Local.IntegralType.identity s) b x = {x} := by
  have := D.identitySource_isIso hg hdegree hs h hIsogenyQuotient
  rw [Data.SphericalPELAlbaneseData.neighbors, Correspondences.EtaleCorrespondence.neighbors_of_source_iso,
    D.identity_targetMap_eq_id hg hdegree hs h hIsogenyQuotient, Category.comp_id]

end

/-! The geometric unit has the correctly normalized algebraic trace:
it is the original Albanese map, as an equality over the number field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (h : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient)

include hg hdegree hs hIsogenyQuotient in
theorem Data.SphericalPELAlbaneseData.albaneseTrace_identity : D.albaneseTrace h (Local.IntegralType.identity s) = D.albaneseMap h := by
  have := D.genericSpace_reduced h
  have := D.albaneseGroup_separated h
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ b x
  rw [D.albaneseTrace_geometric h]
  change ((D.neighbors (Local.IntegralType.identity s) b x).map (fun y => y ≫ D.albaneseMap h)).prod = _
  rw [D.identity_neighbors hg hdegree hs h hIsogenyQuotient b x, Multiset.map_singleton, Multiset.prod_singleton]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
