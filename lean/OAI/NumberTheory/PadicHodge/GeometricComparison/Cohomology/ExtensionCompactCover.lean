import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.ExtensionAffineCover
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.OpenCover

/-! # Extension Compact Cover -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology

noncomputable section

/-! A cohomology extension has a lift on one affine cover of every quasi-compact site object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.OpenCover.Construction

universe u
variable {X : Scheme.{u}} {F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
  (E : ExtensionOf.CohomologyExtension.Extension X F)

theorem ExtensionOf.CohomologyExtension.Extension.exists_compact_cover_lift (U : X.ProEt) [CompactSpace U.left] :
    ∃ (T : X.ProEt) (g : T ⟶ U),
      IsAffine T.left ∧ Surjective g.left ∧ Nonempty (E.Fiber T) := by
  let V := U.left.affineCover.finiteSubcover
  let D := AlgebraicGeometry.FormalGeometry.Completion.ProEtale.OpenCover.Construction.proEtaleOpenCoverObject U V
  have (i : V.I₀) : IsAffine (D i).left := by
    exact inferInstanceAs (IsAffine (U.left.affineCover.X _))
  choose T g hT hg hs using fun i => E.exists_affine_cover_lift (D i)
  let : ∀ i, IsAffine (T i).left := hT
  let p (i : V.I₀) : T i ⟶ U := g i ≫ AlgebraicGeometry.FormalGeometry.Completion.ProEtale.OpenCover.Construction.proEtaleOpenCoverMap U V i
  obtain ⟨s, _, _⟩ := AlgebraicGeometry.FormalGeometry.Completion.ProEtale.DisjointSections.Construction.proEtaleSheaf_disjoint_sections T E.fiberSheaf
    (fun i => Classical.choice (hs i))
  refine ⟨AlgebraicGeometry.FormalGeometry.Completion.ProEtale.DisjointSections.Construction.proEtaleDisjointUnion T, AlgebraicGeometry.FormalGeometry.Completion.ProEtale.DisjointSections.Construction.proEtaleDisjointDesc T p, ?_, ?_, ⟨s⟩⟩
  · change IsAffine (∐ (fun i => (T i).left))
    infer_instance
  · constructor
    intro x
    obtain ⟨i, y, hy⟩ := V.exists_eq x
    let : Surjective (g i).left := hg i
    obtain ⟨z, hz⟩ := (g i).left.surjective y
    refine ⟨Sigma.ι (fun i => (T i).left) i z, ?_⟩
    change (Sigma.desc (fun i => (p i).left)) (Sigma.ι (fun i => (T i).left) i z) = x
    apply (congrArg (fun k : (T i).left ⟶ U.left => k z)
      (Sigma.ι_comp_desc (fun i => (p i).left) i)).trans
    change (V.f i) ((g i).left z) = x
    rw [hz]
    exact hy

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology
