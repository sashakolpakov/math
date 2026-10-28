import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.LocalIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BundleIsoSheaf

/-! # Bundle Picard Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.BundlePicardClass

noncomputable section

/-! A bundle on a family determines a relative Picard class at the identity test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} (P : Over S)

theorem familySchemeFunctor_map_snd {U V : Over S} (f : U ⟶ V) :
    (Picard.PicardSheaf.familySchemeFunctor P).map f ≫ Limits.pullback.snd V.hom P.hom =
      Limits.pullback.snd U.hom P.hom := by
  change (f ▷ P).left ≫ Limits.pullback.snd V.hom P.hom = _
  simp only [Over.whiskerRight_left, Limits.pullback.map, Limits.pullback.lift_snd, Category.comp_id]

def globalBundleFamilyPullbackIso (L : Line.Bundles.LineBundle P.left) {U V : Over S} (f : U ⟶ V) :
    ((L.pullback (Limits.pullback.snd V.hom P.hom)).pullback ((Picard.PicardSheaf.familySchemeFunctor P).map f)).sheaf ≅
      (L.pullback (Limits.pullback.snd U.hom P.hom)).sheaf :=
  (Scheme.Modules.pullbackComp ((Picard.PicardSheaf.familySchemeFunctor P).map f) (Limits.pullback.snd V.hom P.hom)).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (familySchemeFunctor_map_snd P f)).app L.sheaf

def globalBundlePicardClass (L : Line.Bundles.LineBundle P.left) : Picard.PicardSheaf.PicardSections P (Over.mk (𝟙 S)) :=
  (Picard.PicardSheaf.toRelativePicard P).app (.op (Over.mk (𝟙 S)))
    (Line.Bundles.LineBundle.classOf (L.pullback (Limits.pullback.snd (𝟙 S) P.hom)))

def globalBundlePicardIsoSieve (L M : Line.Bundles.LineBundle P.left) : Sieve (Over.mk (𝟙 S)) :=
  Picard.LocalIsomorphisms.picardBundleIsoSieve P (Over.mk (𝟙 S))
    (L.pullback (Limits.pullback.snd (𝟙 S) P.hom)) (M.pullback (Limits.pullback.snd (𝟙 S) P.hom))

theorem globalBundlePicardIsoSieve_mem (L M : Line.Bundles.LineBundle P.left)
    (h : globalBundlePicardClass P L = globalBundlePicardClass P M) :
    globalBundlePicardIsoSieve P L M ∈ (Scheme.fppfTopology.over S) (Over.mk (𝟙 S)) :=
  Picard.LocalIsomorphisms.picardBundleIsoSieve_mem_of_class_eq P (Over.mk (𝟙 S)) _ _ h

theorem globalBundlePicardIsoSieve_apply (L M : Line.Bundles.LineBundle P.left)
    {U : Over S} (f : U ⟶ Over.mk (𝟙 S)) :
    globalBundlePicardIsoSieve P L M f ↔
      Nonempty ((Relative.BundleIsoSheaf.relativeBundleIsoPresheaf P.hom L M).obj (.op U)) := by
  rw [globalBundlePicardIsoSieve, Picard.LocalIsomorphisms.picardBundleIsoSieve_apply]
  constructor
  · rintro ⟨e⟩
    exact ⟨(globalBundleFamilyPullbackIso P L f).symm ≪≫ e ≪≫ globalBundleFamilyPullbackIso P M f⟩
  · rintro ⟨e⟩
    exact ⟨globalBundleFamilyPullbackIso P L f ≪≫ e ≪≫ (globalBundleFamilyPullbackIso P M f).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.BundlePicardClass
