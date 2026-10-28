import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OpenPullbackMapGluing

/-! # Basis Pullback Map Gluing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BasisPullbackMapGluing.Construction

noncomputable section

/-! Maps on a basis of opens glue from their actual refinement equations.
This allows norm constructions to use affine opens only. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v
variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type v}

def compatibleBasisPullbackMaps (B : ι → X.Opens)
    (a : ∀ i, (Scheme.Modules.pullback (B i).ι).obj M ⟶
      (Scheme.Modules.pullback (B i).ι).obj N)
    (ha : ∀ i j (h : B i ≤ B j),
      OpenPullbackMapGluing.Construction.refinePullbackMapTo (X.homOfLE h) (B j).ι (B i).ι (X.homOfLE_ι h) (a j) = a i) :
    AbelianModuli.HilbertConstruction.Module.MapBasisExtension.ModuleBasisMap B M N where
  app i := AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.openPullbackModuleValue (B i).ι (a i) (B i) (by rw [(B i).opensRange_ι])
  naturality i j h s := by
    have hi : B i ≤ (B i).ι.opensRange := by rw [(B i).opensRange_ι]
    have hij : B i ≤ (B j).ι.opensRange := by rwa [(B j).opensRange_ι]
    have hj : B j ≤ (B j).ι.opensRange := by rw [(B j).opensRange_ι]
    have he : AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.openPullbackModuleValue (B i).ι (a i) (B i) hi =
        AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.openPullbackModuleValue (B j).ι (a j) (B i) hij :=
      (congrArg (fun b => AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.openPullbackModuleValue (B i).ι b (B i) hi) (ha i j h)).symm.trans
        (OpenPullbackMapGluing.Construction.openPullbackModuleValue_refineTo (X.homOfLE h) (B j).ι (B i).ι
          (X.homOfLE_ι h) (a j) (B i) hi hij)
    rw [he]
    rw [← AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.openPullbackModuleValue_restriction (B j).ι (a j) (B i) hij,
      ← AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.openPullbackModuleValue_restriction (B j).ι (a j) (B j) hj]
    exact AbelianModuli.HilbertConstruction.OpenModule.MapValues.openModuleMapValue_natural (B j).ι
      (AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.pullbackModuleRestrictionMap (B j).ι (a j)) h hj hij s

theorem basisPullbackMaps_extend_app (B : ι → X.Opens) (hB : Opens.IsBasis (Set.range B))
    (a : ∀ i, (Scheme.Modules.pullback (B i).ι).obj M ⟶
      (Scheme.Modules.pullback (B i).ι).obj N)
    (ha : ∀ i j (h : B i ≤ B j),
      OpenPullbackMapGluing.Construction.refinePullbackMapTo (X.homOfLE h) (B j).ι (B i).ι (X.homOfLE_ι h) (a j) = a i)
    (i : ι) (s : Γ(M, B i)) :
    ((compatibleBasisPullbackMaps B a ha).extend hB).app (B i) s =
      AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.openPullbackModuleValue (B i).ι (a i) (B i) (by rw [(B i).opensRange_ι]) s :=
  (compatibleBasisPullbackMaps B a ha).extend_app hB i s

theorem openModuleMapValue_injective_on_basis {Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (B : ι → X.Opens)
    (hB : Opens.IsBasis (Set.range B)) (φ ψ : M.restrict f ⟶ N.restrict f)
    (h : ∀ i (hi : B i ≤ f.opensRange),
      AbelianModuli.HilbertConstruction.OpenModule.MapValues.openModuleMapValue f φ (B i) hi = AbelianModuli.HilbertConstruction.OpenModule.MapValues.openModuleMapValue f ψ (B i) hi) : φ = ψ := by
  apply AbelianModuli.HilbertConstruction.OpenModule.MapRecovery.openModuleMapValue_injective f φ ψ
  intro U hU
  apply LinearMap.ext
  intro s
  apply N.isSheaf.section_ext
  intro x hx
  obtain ⟨V, ⟨i, rfl⟩, hxi, hi⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨B i, hi, hxi, ?_⟩
  exact (AbelianModuli.HilbertConstruction.OpenModule.MapValues.openModuleMapValue_natural f φ hi hU (hi.trans hU) s).symm.trans
    ((LinearMap.congr_fun (h i (hi.trans hU)) _).trans
      (AbelianModuli.HilbertConstruction.OpenModule.MapValues.openModuleMapValue_natural f ψ hi hU (hi.trans hU) s))

theorem basisPullbackMaps_extend_pullback (B : ι → X.Opens) (hB : Opens.IsBasis (Set.range B))
    (a : ∀ i, (Scheme.Modules.pullback (B i).ι).obj M ⟶
      (Scheme.Modules.pullback (B i).ι).obj N)
    (ha : ∀ i j (h : B i ≤ B j),
      OpenPullbackMapGluing.Construction.refinePullbackMapTo (X.homOfLE h) (B j).ι (B i).ι (X.homOfLE_ι h) (a j) = a i)
    (j : ι) :
    (Scheme.Modules.pullback (B j).ι).map ((compatibleBasisPullbackMaps B a ha).extend hB) = a j := by
  let D := compatibleBasisPullbackMaps B a ha
  have hr : (Scheme.Modules.restrictFunctor (B j).ι).map (D.extend hB) =
      AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.pullbackModuleRestrictionMap (B j).ι (a j) := by
    apply openModuleMapValue_injective_on_basis (B j).ι B hB
    intro i hi
    have hij : B i ≤ B j := by simpa only [(B j).opensRange_ι] using hi
    have hiR : B i ≤ (B i).ι.opensRange := by rw [(B i).opensRange_ι]
    rw [AbelianModuli.HilbertConstruction.OpenModule.MapValues.openModuleMapValue_from_global, AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.openPullbackModuleValue_restriction]
    apply LinearMap.ext
    intro s
    exact (D.extend_app hB i s).trans
      (LinearMap.congr_fun
        ((congrArg (fun a => AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues.openPullbackModuleValue (B i).ι a (B i) hiR)
          (ha i j hij)).symm.trans
          (OpenPullbackMapGluing.Construction.openPullbackModuleValue_refineTo (X.homOfLE hij) (B j).ι (B i).ι
            (X.homOfLE_ι hij) (a j) (B i) hiR hi)) s)
  let c := Scheme.Modules.restrictFunctorIsoPullback (B j).ι
  apply (cancel_epi (c.hom.app M)).mp
  exact (c.hom.naturality (D.extend hB)).symm.trans
    ((congrArg (fun a => a ≫ c.hom.app N) hr).trans (by
      change (c.hom.app M ≫ a j ≫ c.inv.app N) ≫ c.hom.app N = _
      simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BasisPullbackMapGluing.Construction
