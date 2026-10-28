import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Local
import OAI.AlgebraicGeometry.Resolution.Blowups.ChartFlatBaseChange

/-! # Reduced Global Blowup Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ReducedGlobalBlowupLift.Construction

noncomputable section

section

/-! Regular principal native generators persist on smaller affine opens without integrality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affineRestriction_flat {X : Scheme} {U V : X.affineOpens} (hVU : V ≤ U) :
    (Blowup.Functor.Construction.affineRestriction hVU).Flat := by
  have h : V.1 ≤ (𝟙 X) ⁻¹ᵁ U.1 := hVU
  have hf := Scheme.Hom.flat_appLE (𝟙 X) U.2 V.2 h
  have hOp : V.1 ≤ U.1 := hVU
  have he : Scheme.Hom.appLE (𝟙 X) U.1 V.1 h = X.presheaf.map (homOfLE hOp).op := by
    change (𝟙 Γ(X, U) ≫ X.presheaf.map (homOfLE hOp).op) = X.presheaf.map (homOfLE hOp).op
    exact Category.id_comp _
  rw [he] at hf
  exact hf

theorem affineRestriction_regular {X : Scheme} {U V : X.affineOpens} (hVU : V ≤ U)
    (r : Γ(X, U)) (hr : IsRegular r) : IsRegular (Blowup.Functor.Construction.affineRestriction hVU r) := by
  let : Algebra Γ(X, U) Γ(X, V) := (Blowup.Functor.Construction.affineRestriction hVU).toAlgebra
  let : Module.Flat Γ(X, U) Γ(X, V) := affineRestriction_flat hVU
  exact ChartFlatBaseChange.Construction.flat_algebraMap_regular r hr

theorem regular_principal_generators_within
    {X : Scheme} (I : X.IdealSheafData)
    (hlocal : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ r : Γ(X, U), IsRegular r ∧ I.ideal U = Ideal.span {r})
    (O : X.Opens) (x : X) (hx : x ∈ O) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ O ∧
      ∃ r : Γ(X, U), IsRegular r ∧ I.ideal U = Ideal.span {r} := by
  obtain ⟨U, hxU, r, hr, hgen⟩ := hlocal x
  obtain ⟨W, hW, hxW, hsub⟩ := exists_isAffineOpen_mem_and_subset (U := U.1 ⊓ O) (x := x) ⟨hxU, hx⟩
  let V : X.affineOpens := ⟨W, hW⟩
  have hVU : V ≤ U := hsub.trans inf_le_left
  exact ⟨V, hxW, hsub.trans inf_le_right, Blowup.Functor.Construction.affineRestriction hVU r,
    affineRestriction_regular hVU r hr, Locally.PrincipalIdealSheaf.Construction.principal_idealSheaf_restrict I hVU r hgen⟩

end

/-! Actual global blowup lifts from reduced sources with regular local center generators. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem exists_local_globalBlowup_lift_of_regular_generators
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (q : Y ⟶ X)
    (hlocal : ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧
      ∃ r : Γ(Y, U), IsRegular r ∧ (I.comap q).ideal U = Ideal.span {r}) (y : Y) :
    ∃ W : Y.affineOpens, y ∈ W.1 ∧
      ∃ l : Spec Γ(Y, W) ⟶ GlobalBlowup.Data.Construction.globalBlowup I hI, l ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI = W.2.fromSpec ≫ q := by
  obtain ⟨U, hU, hqy, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := q y) trivial
  let A : X.affineOpens := ⟨U, hU⟩
  obtain ⟨W, hyW, hWA, r, hr, he⟩ := regular_principal_generators_within (I.comap q)
    hlocal (q ⁻¹ᵁ A.1) y hqy
  let φ := (q.appLE A.1 W.1 hWA).hom
  have hgen : (I.ideal A).map φ = Ideal.span {r} :=
    (IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I q A W hWA).symm.trans he
  let a : (I.ideal A).map φ := ⟨r, hgen ▸ Ideal.mem_span_singleton_self r⟩
  refine ⟨W, hyW, Blowup.BlowupLift.Construction.affineBlowupLift (I.ideal A) φ a hgen hr ≫ GlobalBlowup.Data.Construction.globalBlowupChart I hI A, ?_⟩
  rw [Category.assoc, GlobalBlowup.Data.Construction.globalBlowupChart_over, ← Category.assoc, Blowup.BlowupLift.Construction.affineBlowupLift_over]
  exact IsAffineOpen.SpecMap_appLE_fromSpec q A.2 W.2 hWA

theorem existsUnique_globalBlowup_lift_of_regular_generators
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [IsReduced Y]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (q : Y ⟶ X)
    (hdense : Dense ((q ⁻¹ᵁ I.support.compl : Y.Opens) : Set Y))
    (hlocal : ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧
      ∃ r : Γ(Y, U), IsRegular r ∧ (I.comap q).ideal U = Ideal.span {r}) :
    ∃! l : Y ⟶ GlobalBlowup.Data.Construction.globalBlowup I hI, l ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI = q := by
  choose W hW l hl using exists_local_globalBlowup_lift_of_regular_generators I hI q hlocal
  let : ∀ y, IsOpenImmersion (W y).2.fromSpec := fun y => (W y).2.isOpenImmersion_fromSpec
  let C : Y.OpenCover := Scheme.Cover.mkOfCovers Y (fun y => Spec Γ(Y, W y))
    (fun y => (W y).2.fromSpec) (by
      intro y
      refine ⟨y, ?_⟩
      change y ∈ (W y).2.fromSpec.opensRange
      rw [(W y).2.opensRange_fromSpec]
      exact hW y) (fun _ => inferInstance)
  have hcompat (y z : C.I₀) : pullback.fst (C.f y) (C.f z) ≫ l y = pullback.snd (C.f y) (C.f z) ≫ l z := by
    let : IsOpenImmersion (C.f y) := C.map_prop y
    let : IsOpenImmersion (C.f z) := C.map_prop z
    let t := pullback.fst (C.f y) (C.f z) ≫ C.f y
    let : IsReduced (pullback (C.f y) (C.f z)) := isReduced_of_isOpenImmersion t
    apply GlobalBlowup.Local.Construction.globalBlowup_hom_ext_of_dense_complement I hI (t ≫ q)
      (hdense.preimage t.isOpenEmbedding.isOpenMap)
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun u => pullback.fst (C.f y) (C.f z) ≫ u) (hl y)).trans
          (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun u => pullback.snd (C.f y) (C.f z) ≫ u) (hl z)).trans
          ((pullback.condition_assoc (f := C.f y) (g := C.f z) q).symm.trans (Category.assoc _ _ _).symm))
  let g := C.glueMorphisms l hcompat
  have hg : g ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI = q := by
    apply C.hom_ext
    intro y
    rw [← Category.assoc, C.ι_glueMorphisms l hcompat y]
    exact hl y
  exact ⟨g, hg, fun a ha => GlobalBlowup.Local.Construction.globalBlowup_hom_ext_of_dense_complement I hI q hdense a g ha hg⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ReducedGlobalBlowupLift.Construction
