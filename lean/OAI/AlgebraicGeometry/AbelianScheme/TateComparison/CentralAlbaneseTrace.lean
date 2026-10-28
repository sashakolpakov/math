import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralGeometricTargets
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralBranches
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseTrace

/-! # Central Albanese Trace -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

section

/-! The actual central correspondence is the graph of the constructed
marking automorphism, with its precise singleton geometric neighbors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

include hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.centralTargetMap_eq_marking :
    D.centralTargetMap hg hdegree hs hgeometry hIsogenyQuotient = (D.qMarkingAutomorphism hgeometry hg.2.2.1).hom := by
  have := D.genericSpace_reduced hgeometry
  have : IsProper D.model.space.hom := hgeometry.proper
  have : IsSeparated D.space.hom := inferInstanceAs
    (IsSeparated (CategoryTheory.Limits.pullback.snd D.model.space.hom D.generic))
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ b x
  let c : (D.correspondence (Local.IntegralType.central s)).Fiber x :=
    ⟨x ≫ (D.centralSourceIso hg hdegree hs hgeometry hIsogenyQuotient).inv, by
      change x ≫ (D.centralSourceIso hg hdegree hs hgeometry hIsogenyQuotient).inv ≫
        (D.centralSourceIso hg hdegree hs hgeometry hIsogenyQuotient).hom = x
      rw [Iso.inv_hom_id, Category.comp_id]⟩
  exact (Category.assoc _ _ _).symm.trans
    (D.centralEndpoint_eq_marking hg hgeometry hdegree hs hIsogenyQuotient hElementaryDivisors b x c)

include hdegree hs hIsogenyQuotient hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.isCentralGraph_qMarking :
    D.IsCentralGraph (D.qMarkingAutomorphism hgeometry hg.2.2.1) := by
  refine ⟨D.centralSourceIso hg hdegree hs hgeometry hIsogenyQuotient, rfl, ?_⟩
  rw [← D.centralTargetMap_eq_marking hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors]
  exact (D.centralTargetMap_factor hg hdegree hs hgeometry hIsogenyQuotient).symm

include hdegree hs hIsogenyQuotient hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.central_neighbors_marking {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b) :
    D.neighbors (Local.IntegralType.central s) b x = {x ≫ (D.qMarkingAutomorphism hgeometry hg.2.2.1).hom} := by
  rw [D.central_neighbors hg hdegree hs hgeometry hIsogenyQuotient b x,
    D.centralTargetMap_eq_marking hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors]

end

/-! The central algebraic trace is the Albanese map composed with the
actual marking automorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

include hdegree hs hIsogenyQuotient hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.albaneseTrace_central : D.albaneseTrace hgeometry (Local.IntegralType.central s) =
    (D.qMarkingAutomorphism hgeometry hg.2.2.1).hom ≫ D.albaneseMap hgeometry := by
  have : IsReduced D.space.left := D.genericSpace_reduced hgeometry
  have : IsSeparated D.albaneseGroup.X.hom := D.albaneseGroup_separated hgeometry
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ b x
  have he := congrArg (fun m : Multiset (D.GeometricPoint b) =>
    (m.map (fun y => y ≫ D.albaneseMap hgeometry)).prod)
      (D.central_neighbors_marking hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors b x)
  have he' : (((D.correspondence (Local.IntegralType.central s)).neighbors b x).map
      (fun y => y ≫ D.albaneseMap hgeometry)).prod =
      (x ≫ (D.qMarkingAutomorphism hgeometry hg.2.2.1).hom) ≫ D.albaneseMap hgeometry := by
    simpa only [Multiset.map_singleton, Multiset.prod_singleton] using he
  exact (D.albaneseTrace_geometric hgeometry _ b x).trans (he'.trans (Category.assoc _ _ _))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
