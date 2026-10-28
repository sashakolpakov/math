import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OpenDescentComparison

/-! # Line Hom Descent -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LineHomDescent

noncomputable section

/-! Effective fpqc descent of morphisms and isomorphisms between actual
line bundles, proved using local frames and native open gluing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedSquares
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OpenDescentComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LocalDescentGluing OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FaithfulLinePullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f]
variable {M N : Y.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N)

include hM hN in
theorem existsUnique_lineHom_descent
    (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (hq : FramedDescent.CompatibleHom f q) :
    ∃! a : M ⟶ N, (Scheme.Modules.pullback f).map a = q := by
  have hN₀ := hN
  choose U hyU heM using hM
  choose V hyV heN using hN
  let W (y : Y) := U y ⊓ V y
  have hW : (⊤ : Y.Opens) ≤ iSup W := by
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y, hyV y⟩
  let qW (y : Y) :
      (Scheme.Modules.pullback (f ∣_ W y)).obj ((Scheme.Modules.pullback (W y).ι).obj M) ⟶
        (Scheme.Modules.pullback (f ∣_ W y)).obj ((Scheme.Modules.pullback (W y).ι).obj N) :=
    (NormalizedSquares.sectionSquareIso f (W y).ι (f ⁻¹ᵁ W y).ι (f ∣_ W y) (morphismRestrict_ι f (W y)).symm).inv.app M ≫
      (Scheme.Modules.pullback (f ⁻¹ᵁ W y).ι).map q ≫
        (NormalizedSquares.sectionSquareIso f (W y).ι (f ⁻¹ᵁ W y).ι (f ∣_ W y) (morphismRestrict_ι f (W y)).symm).hom.app N
  have hlocal (y : Y) : ∃ a : (Scheme.Modules.pullback (W y).ι).obj M ⟶
      (Scheme.Modules.pullback (W y).ι).obj N,
      (Scheme.Modules.pullback (f ∣_ W y)).map a = qW y := by
    let g := f ∣_ W y
    have : Flat g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f (W y)).flip (inferInstanceAs (Flat f))
    have : Surjective g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f (W y)).flip (inferInstanceAs (Surjective f))
    have : QuasiCompact g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f (W y)).flip (inferInstanceAs (QuasiCompact f))
    let eM := ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction.Construction.restrictLineBundleTrivialization (show W y ≤ U y from inf_le_left)
      (Classical.choice (heM y))
    let eN := ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction.Construction.restrictLineBundleTrivialization (show W y ≤ V y from inf_le_right)
      (Classical.choice (heN y))
    have hqW : FramedDescent.CompatibleHom g (qW y) :=
      Intrinsic.CompatibleBaseChange.baseHom_compatible f g (f ⁻¹ᵁ W y).ι (W y).ι
        (morphismRestrict_ι f (W y)).symm q hq
    exact (FramedDescent.existsUnique_framedHom_descent g eM eN (qW y) hqW).exists
  choose a ha using hlocal
  exact LocalDescentGluing.existsUnique_hom_of_local_descent f hN₀ q W hW
    (fun y ↦ OpenDescentComparison.restrictedMorphism (W y) (a y))
    (fun y ↦ OpenDescentComparison.descent_square_of_native f (W y) q (a y) (ha y))

include hM hN in
theorem existsUnique_lineIso_descent
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    (he : FramedDescent.CompatibleHom f e.hom) :
    ∃! d : M ≅ N, (Scheme.Modules.pullback f).mapIso d = e := by
  obtain ⟨a, ha, hu⟩ := existsUnique_lineHom_descent f hM hN e.hom he
  obtain ⟨b, hb, _⟩ := existsUnique_lineHom_descent f hN hM e.inv (FramedDescent.compatibleHom_inverse f e he)
  let L := Scheme.Modules.pullback f
  have hab : a ≫ b = 𝟙 M := by
    apply FaithfulLinePullback.linePullback_injective f hM hM
    exact (L.map_comp a b).trans ((congrArg₂ (fun r s ↦ r ≫ s) ha hb).trans
      (e.hom_inv_id.trans (L.map_id M).symm))
  have hba : b ≫ a = 𝟙 N := by
    apply FaithfulLinePullback.linePullback_injective f hN hN
    exact (L.map_comp b a).trans ((congrArg₂ (fun r s ↦ r ≫ s) hb ha).trans
      (e.inv_hom_id.trans (L.map_id N).symm))
  let d : M ≅ N := ⟨a, b, hab, hba⟩
  refine ⟨d, Iso.ext ha, ?_⟩
  intro d' hd'
  apply Iso.ext
  exact hu d'.hom (congrArg Iso.hom hd')

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LineHomDescent
