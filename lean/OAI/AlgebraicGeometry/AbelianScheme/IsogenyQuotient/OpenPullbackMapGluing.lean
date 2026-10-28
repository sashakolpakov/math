import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.RefinementNaturality

/-! # Open Pullback Map Gluing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OpenPullbackMapGluing.Construction

noncomputable section

/-! Glue actual pullback maps on an open cover from agreement after
refinement to every smaller open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v
variable {X Y Z : Scheme.{u}} {M N : Z.Modules}

def refinePullbackMapTo (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k)
    (a : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N) :
    (Scheme.Modules.pullback k).obj M ⟶ (Scheme.Modules.pullback k).obj N :=
  (Scheme.Modules.pullbackCongr h).inv.app M ≫ AbelianModuli.HilbertConstruction.OpenPullback.Refinement.refineOpenPullbackMap f g a ≫
    (Scheme.Modules.pullbackCongr h).hom.app N

theorem openPullbackModuleValue_refineTo
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion k]
    (h : f ≫ g = k)
    (a : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N)
    (U : Z.Opens) (hU : U ≤ k.opensRange) (hUg : U ≤ g.opensRange) :
    AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.openPullbackModuleValue k (refinePullbackMapTo f g k h a) U hU =
      AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.openPullbackModuleValue g a U hUg := by
  subst k
  simpa only [refinePullbackMapTo, Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.refl_inv, Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.comp_id] using
    AbelianModuli.HilbertConstruction.OpenPullback.RefinementNaturality.openPullbackModuleValue_comp f g a U hU

def compatiblePullbackMapsData {ι : Type v} (U : ι → Z.Opens)
    (a : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ⟶
      (Scheme.Modules.pullback (U i).ι).obj N)
    (ha : ∀ i j (V : Z.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      refinePullbackMapTo (Z.homOfLE hi) (U i).ι V.ι (Z.homOfLE_ι hi) (a i) =
        refinePullbackMapTo (Z.homOfLE hj) (U j).ι V.ι (Z.homOfLE_ι hj) (a j)) :
    AbelianModuli.HilbertConstruction.Module.OpenMapGluing.OpenCoverModuleMaps U M N where
  localMap i := AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.pullbackModuleRestrictionMap (U i).ι (a i)
  agree i j V hi hj := by
    have hiR : V ≤ (U i).ι.opensRange := by rwa [(U i).opensRange_ι]
    have hjR : V ≤ (U j).ι.opensRange := by rwa [(U j).opensRange_ι]
    have hV : V ≤ V.ι.opensRange := by rw [V.opensRange_ι]
    exact (AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.openPullbackModuleValue_restriction (U i).ι (a i) V hiR).trans
      ((openPullbackModuleValue_refineTo (Z.homOfLE hi) (U i).ι V.ι
        (Z.homOfLE_ι hi) (a i) V hV hiR).symm.trans
        ((congrArg (fun b => AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.openPullbackModuleValue V.ι b V hV) (ha i j V hi hj)).trans
          ((openPullbackModuleValue_refineTo (Z.homOfLE hj) (U j).ι V.ι
            (Z.homOfLE_ι hj) (a j) V hV hjR).trans
            (AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.openPullbackModuleValue_restriction (U j).ι (a j) V hjR).symm)))

theorem existsUnique_hom_of_refinement_compatibility {ι : Type v} (U : ι → Z.Opens)
    (hU : ∀ z : Z, ∃ i, z ∈ U i)
    (a : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ⟶
      (Scheme.Modules.pullback (U i).ι).obj N)
    (ha : ∀ i j (V : Z.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      refinePullbackMapTo (Z.homOfLE hi) (U i).ι V.ι (Z.homOfLE_ι hi) (a i) =
        refinePullbackMapTo (Z.homOfLE hj) (U j).ι V.ι (Z.homOfLE_ι hj) (a j)) :
    ∃! b : M ⟶ N, ∀ i, (Scheme.Modules.pullback (U i).ι).map b = a i := by
  let D := compatiblePullbackMapsData U a ha
  refine ⟨D.glue hU, ?_, ?_⟩
  · intro i
    have he := D.glue_restrict hU i
    let c := Scheme.Modules.restrictFunctorIsoPullback (U i).ι
    apply (cancel_epi (c.hom.app M)).mp
    exact (c.hom.naturality (D.glue hU)).symm.trans
      ((congrArg (fun b => b ≫ c.hom.app N) he).trans (by
        change (c.hom.app M ≫ a i ≫ c.inv.app N) ≫ c.hom.app N = _
        simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]))
  · intro b hb
    apply D.glue_unique hU b
    intro i
    let c := Scheme.Modules.restrictFunctorIsoPullback (U i).ι
    apply (cancel_mono (c.hom.app N)).mp
    exact (c.hom.naturality b).trans
      ((congrArg (fun a => c.hom.app M ≫ a) (hb i)).trans (by
        change c.hom.app M ≫ a i = (c.hom.app M ≫ a i ≫ c.inv.app N) ≫ c.hom.app N
        simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OpenPullbackMapGluing.Construction
