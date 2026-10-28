import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionFrameApps
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleGluingIs

/-! # Section Frame Gluing -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionFrameGluing.Construction

noncomputable section

/-! Line-bundle isomorphisms from covering sections with matching frame coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def sectionFrameAppMap {X : Scheme.{u}} {M N : X.Modules}
    (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (t : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N)
    {U : X.Opens} (hs : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) (ht : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
  ((SectionFrameApps.Construction.sectionAppLinearEquiv s hs).symm.trans (SectionFrameApps.Construction.sectionAppLinearEquiv t ht)).toLinearMap

theorem sectionFrameAppMap_restrict {X : Scheme.{u}} {M N : X.Modules}
    (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (t : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N)
    {U V : X.Opens} (h : V ≤ U)
    (hs : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) (ht : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t) (m : Γ(M, U)) :
    N.presheaf.map (homOfLE h).op (sectionFrameAppMap s t hs ht m) =
      sectionFrameAppMap s t (h.trans hs) (h.trans ht) (M.presheaf.map (homOfLE h).op m) := by
  have hn := PresheafOfModules.naturality_apply t.val (homOfLE h).op
    ((SectionFrameApps.Construction.sectionAppLinearEquiv s hs).symm m)
  exact hn.symm.trans (congrArg (fun r : Γ(X, V) => t.app V r)
    (SectionFrameApps.Construction.sectionAppLinearEquiv_symm_restrict s h hs m))

theorem sectionFrameAppMap_eq {X : Scheme.{u}} {M N : X.Modules}
    (s s' : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (t t' : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N)
    {U : X.Opens} (hs : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) (hs' : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s')
    (ht : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t) (ht' : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t')
    (h : ∀ r : Γ(X, U), (SectionFrameApps.Construction.sectionAppLinearEquiv s hs).symm (s'.app U r) =
      (SectionFrameApps.Construction.sectionAppLinearEquiv t ht).symm (t'.app U r)) :
    sectionFrameAppMap s t hs ht = sectionFrameAppMap s' t' hs' ht' := by
  apply LinearMap.ext
  intro m
  let r := (SectionFrameApps.Construction.sectionAppLinearEquiv s' hs').symm m
  have hr : s'.app U r = m := (SectionFrameApps.Construction.sectionAppLinearEquiv s' hs').apply_symm_apply m
  change t.app U ((SectionFrameApps.Construction.sectionAppLinearEquiv s hs).symm m) = t'.app U r
  exact (congrArg (fun z : Γ(M, U) => t.app U ((SectionFrameApps.Construction.sectionAppLinearEquiv s hs).symm z)) hr).symm.trans
    ((congrArg (fun z : Γ(X, U) => t.app U z) (h r)).trans
      ((SectionFrameApps.Construction.sectionAppLinearEquiv t ht).apply_symm_apply (t'.app U r)))

theorem lineBundleIso_of_section_coordinates {X : Scheme.{u}} {M N : X.Modules}
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (s : ι → (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)) (t : ι → (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N))
    (hs : ∀ i, U i ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ i, U i ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t i))
    (h : ∀ i j (V : X.Opens) (hi : V ≤ U i) (_hj : V ≤ U j) (r : Γ(X, V)),
      (SectionFrameApps.Construction.sectionAppLinearEquiv (s i) (hi.trans (hs i))).symm ((s j).app V r) =
        (SectionFrameApps.Construction.sectionAppLinearEquiv (t i) (hi.trans (ht i))).symm ((t j).app V r)) :
    Nonempty (M ≅ N) := by
  let D : AlgebraicGeometry.Quotients.FiniteDescent.ModuleGluingIs.Construction.ModuleGluing.Datum M N :=
    { I := ι
      opens := U
      covers := hU
      app := fun i V hi => sectionFrameAppMap (s i) (t i) (hi.trans (hs i)) (hi.trans (ht i))
      naturality := fun i _ _ hV hi m =>
        sectionFrameAppMap_restrict (s i) (t i) hV (hi.trans (hs i)) (hi.trans (ht i)) m
      overlap := fun i j V hi hj =>
        sectionFrameAppMap_eq (s i) (s j) (t i) (t j)
          (hi.trans (hs i)) (hj.trans (hs j)) (hi.trans (ht i)) (hj.trans (ht j)) (h i j V hi hj) }
  have : IsIso D.glue := D.glue_isIso (fun i V hi =>
    ((SectionFrameApps.Construction.sectionAppLinearEquiv (s i) (hi.trans (hs i))).symm.trans
      (SectionFrameApps.Construction.sectionAppLinearEquiv (t i) (hi.trans (ht i)))).bijective)
  exact ⟨asIso D.glue⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionFrameGluing.Construction
