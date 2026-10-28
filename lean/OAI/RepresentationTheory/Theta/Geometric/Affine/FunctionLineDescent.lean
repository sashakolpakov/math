import OAI.RepresentationTheory.Theta.Geometric.FramedFunctionDescent
import OAI.RepresentationTheory.Theta.Geometric.DominantLocalDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenDescentComparison

/-! # Function Line Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.FunctionLineDescent

noncomputable section

/-! Global native line-bundle descent follows from coefficient descent
on affine opens and scheme-theoretic dominance. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedSquares.PicardNormalizedSquares
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenDescentComparison.PicardOpenDescentComparison

variable {X Y : Scheme} (f : X ⟶ Y) [IsSchemeTheoreticallyDominant f] [QuasiCompact f]
    (hf : ∀ U : Y.Opens, IsAffineOpen U → RegularFunctionDescent.HasRegularFunctionDescent (f ∣_ U))
    {M N : Y.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N)

include hf hM hN in
theorem existsUnique_lineHom_of_affine_function_descent
    (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (hq : AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent.CompatibleHom f q) :
    ∃! a : M ⟶ N, (Scheme.Modules.pullback f).map a = q := by
  have hN₀ := hN
  choose U hyU heM using hM
  choose V hyV heN using hN
  have hWexists (y : Y) : ∃ W : Y.Opens, y ∈ W ∧ IsAffineOpen W ∧ W ≤ U y ⊓ V y := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ U y ⊓ V y from ⟨hyU y, hyV y⟩) (U y ⊓ V y).isOpen
    exact ⟨W, hyW, hW, hWU⟩
  choose W hyW haW hleW using hWexists
  have hW : (⊤ : Y.Opens) ≤ iSup W := by
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyW y⟩
  let qW (y : Y) :
      (Scheme.Modules.pullback (f ∣_ W y)).obj ((Scheme.Modules.pullback (W y).ι).obj M) ⟶
        (Scheme.Modules.pullback (f ∣_ W y)).obj ((Scheme.Modules.pullback (W y).ι).obj N) :=
    (AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedSquares.PicardNormalizedSquares.sectionSquareIso f (W y).ι (f ⁻¹ᵁ W y).ι (f ∣_ W y) (morphismRestrict_ι f (W y)).symm).inv.app M ≫
      (Scheme.Modules.pullback (f ⁻¹ᵁ W y).ι).map q ≫
        (AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedSquares.PicardNormalizedSquares.sectionSquareIso f (W y).ι (f ⁻¹ᵁ W y).ι (f ∣_ W y) (morphismRestrict_ι f (W y)).symm).hom.app N
  have hlocal (y : Y) : ∃ a : (Scheme.Modules.pullback (W y).ι).obj M ⟶
      (Scheme.Modules.pullback (W y).ι).obj N,
      (Scheme.Modules.pullback (f ∣_ W y)).map a = qW y := by
    let g := f ∣_ W y
    have : IsSchemeTheoreticallyDominant g :=
      IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict f (W y)).flip
    have : QuasiCompact g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f (W y)).flip (inferInstanceAs (QuasiCompact f))
    let eM := ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction.Construction.restrictLineBundleTrivialization ((hleW y).trans inf_le_left) (Classical.choice (heM y))
    let eN := ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction.Construction.restrictLineBundleTrivialization ((hleW y).trans inf_le_right) (Classical.choice (heN y))
    have hqW : AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent.CompatibleHom g (qW y) :=
      AlgebraicGeometry.PELModuli.IntegralModel.Picard.IntrinsicCompatibleBaseChange.PicardIntrinsicCompatibleBaseChange.baseHom_compatible f g (f ⁻¹ᵁ W y).ι (W y).ι
        (morphismRestrict_ι f (W y)).symm q hq
    exact (FramedFunctionDescent.existsUnique_framedHom_of_function_descent g (g.app_injective ⊤) (hf (W y) (haW y))
      eM eN (qW y) hqW).exists
  choose a ha using hlocal
  exact DominantLocalDescent.IntrinsicDominantPullback.existsUnique_hom_of_local_descent f hN₀ q W hW
    (fun y => AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenDescentComparison.PicardOpenDescentComparison.restrictedMorphism (W y) (a y))
    (fun y => AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenDescentComparison.PicardOpenDescentComparison.descent_square_of_native f (W y) q (a y) (ha y))

include hf hM hN in
theorem existsUnique_lineIso_of_affine_function_descent
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    (he : AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent.CompatibleHom f e.hom) :
    ∃! d : M ≅ N, (Scheme.Modules.pullback f).mapIso d = e := by
  obtain ⟨a, ha, hu⟩ := existsUnique_lineHom_of_affine_function_descent f hf hM hN e.hom he
  obtain ⟨b, hb, _⟩ := existsUnique_lineHom_of_affine_function_descent f hf hN hM e.inv
    (AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent.compatibleHom_inverse f e he)
  have hab : a ≫ b = 𝟙 M := by
    apply DominantLinePullback.IntrinsicDominantPullback.linePullback_injective f hM hM
    dsimp only
    rw [CategoryTheory.Functor.map_comp, ha, hb, e.hom_inv_id, CategoryTheory.Functor.map_id]
  have hba : b ≫ a = 𝟙 N := by
    apply DominantLinePullback.IntrinsicDominantPullback.linePullback_injective f hN hN
    dsimp only
    rw [CategoryTheory.Functor.map_comp, hb, ha, e.inv_hom_id, CategoryTheory.Functor.map_id]
  refine ⟨⟨a, b, hab, hba⟩, Iso.ext ha, ?_⟩
  intro d hd
  exact Iso.ext (hu d.hom (congrArg Iso.hom hd))

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.FunctionLineDescent
