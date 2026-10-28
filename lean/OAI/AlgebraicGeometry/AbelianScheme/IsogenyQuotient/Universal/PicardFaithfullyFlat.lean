import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.BundleNormalization
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization

/-! # Picard Faithfully Flat -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.PicardFaithfullyFlat.Construction

noncomputable section

/-! Relative Picard equality between actual line bundles descends
through a faithfully flat quasi-compact parameter change when the
original abelian family has universal global functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

theorem fpqcSingletonOverSieve_mem {S : Scheme.{0}} {U T : Over S} (u : U ⟶ T)
    [Flat u.left] [QuasiCompact u.left] [Surjective u.left] :
    Sieve.ofArrows (fun _ : PUnit.{1} => U) (fun _ => u) ∈ (Scheme.fpqcTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using
    Precoverage.generate_mem_toGrothendieck u.left.singleton_mem_fpqcPrecoverage

set_option backward.isDefEq.respectTransparency false in
theorem universal_normalized_lineIso_of_faithfullyFlat_picard_eq
    {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A.scheme)
    {T U : Over S} (u : U ⟶ T) [Flat u.left] [Surjective u.left] [QuasiCompact u.left]
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left)
    (eL : (L.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)
    (eM : (M.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (u ▷ A.scheme).left)) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (M.pullback (u ▷ A.scheme).left))) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  have hz (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left)
      (eQ : (Q.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left) :
      ((Q.pullback (u ▷ A.scheme).left).pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left).sheaf ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.left := by
    exact (Scheme.Modules.pullbackComp (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left (u ▷ A.scheme).left).app Q.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A u))).app Q.sheaf ≪≫
      (Scheme.Modules.pullbackComp u.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).symm.app Q.sheaf ≪≫
      (Scheme.Modules.pullback u.left).mapIso eQ ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso u.left
  obtain ⟨e⟩ := BundleNormalization.Construction.universal_bundleIso_of_relativePicard_eq A.scheme U hA
    (L.pullback (u ▷ A.scheme).left) (M.pullback (u ▷ A.scheme).left)
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection A U) ((hz L eL) ≪≫ (hz M eM).symm) h
  let R := AbelianModuli.HilbertConstruction.Picard.LocalIsomorphisms.picardBundleIsoSieve A.scheme T L M
  have hR : R ∈ (Scheme.fpqcTopology.over S) T := by
    apply (Scheme.fpqcTopology.over S).superset_covering
      ((Sieve.generate_le_iff _ _).mpr ?_) (fpqcSingletonOverSieve_mem u)
    intro V v hv
    obtain ⟨i⟩ := hv
    exact (AbelianModuli.HilbertConstruction.Picard.LocalIsomorphisms.picardBundleIsoSieve_apply A.scheme T L M u).mpr ⟨e⟩
  let p := CategoryTheory.Limits.pullback.fst T.hom A.scheme.hom
  have hF : GlobalFunctions.Construction.HasUniversalGlobalFunctions (Over.mk p) :=
    hA.of_isPullback (CategoryTheory.Limits.pullback.snd T.hom A.scheme.hom) p T.hom
      (IsPullback.of_hasPullback T.hom A.scheme.hom).flip
  apply (AbelianModuli.HilbertConstruction.IsoIdentityBaseChange.relativeBundleIso_identity_nonempty_iff p L M).mp
  apply AbelianModuli.HilbertConstruction.Normalized.BundleIsoDescent.relativeBundleIso_nonempty_of_cover p (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection A T) L M (eL ≪≫ eM.symm) Scheme.fpqcTopology
    (BundleNormalization.Construction.universal_familyBaseChangeSection_bijective p (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
      (Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection A T) hF) (Over.mk (𝟙 T.left)) (AbelianModuli.HilbertConstruction.Module.HomLocalSheaf.sliceBaseChangeSieve T R)
    (AbelianModuli.HilbertConstruction.Picard.TestBaseSieve.sliceBaseChangeSieve_mem T Scheme.fpqcTopology R hR)
  intro V v hv
  exact AbelianModuli.HilbertConstruction.Picard.TestBundleTransport.picardTestBaseChange_local_iso A.scheme T V L M (AbelianModuli.HilbertConstruction.Picard.TestBaseSieve.sliceBaseChangeSieve_mem_testBaseArrow T R v hv)

set_option backward.isDefEq.respectTransparency false in
theorem universal_relativePicard_eq_of_faithfullyFlat
    {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A.scheme)
    {T U : Over S} (u : U ⟶ T) [Flat u.left] [Surjective u.left] [QuasiCompact u.left]
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left)
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (u ▷ A.scheme).left)) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (M.pullback (u ▷ A.scheme).left))) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) := by
  let L' := FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.scheme T L
  let M' := FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.scheme T M
  have hn (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left) :
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.scheme T Q)) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) :=
    (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T))
      (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_class A.scheme T Q)).trans
        (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_relative A.scheme T (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q))
  have hnorm : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L'.pullback (u ▷ A.scheme).left)) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (M'.pullback (u ▷ A.scheme).left)) := by
    have hleft := AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme u (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L')
    have hright := AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme u (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M')
    have hm := congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).obj.map u.op) (hn L)
    have hnM := congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).obj.map u.op) (hn M)
    exact hleft.symm.trans (hm.trans ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme u
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).trans (h.trans ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme u
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)).symm.trans (hnM.symm.trans hright)))))
  have he := universal_normalized_lineIso_of_faithfullyFlat_picard_eq A hA u L' M'
    (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis A.scheme T L) (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis A.scheme T M) hnorm
  exact (hn L).symm.trans ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T))
    (Quotient.sound he)).trans (hn M))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.PicardFaithfullyFlat.Construction
