import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionExtension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Addition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroTensorPowers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Powers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Ample Quasi Finite Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleQuasiFinitePullback

noncomputable section

/-! Pulling an ample line bundle back along a separated quasi-finite
finite-type morphism. Section extension first gives affine nonvanishing
neighborhoods inside any prescribed open; Zariski's main theorem then
reduces the pullback to an open immersion and an affine morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}}

theorem ample_power_section_neighborhood [Y.IsSeparated]
    (L : HilbertConstruction.Line.Bundles.LineBundle Y) (hL : L.IsAmple) (U : Y.Opens) (y : Y) (hy : y ∈ U) :
    ∃ (n : ℕ) (_ : 0 < n) (s : HilbertConstruction.Line.Bundles.structureModule Y ⟶ (L.tensorPower n).sheaf),
      y ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ∧ IsAffineOpen (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) ∧
        HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ≤ U := by
  have : CompactSpace Y := ⟨hL.1⟩
  obtain ⟨d, hd, s, hys, hs⟩ := (L.isAmple_iff_tensorPower.mp hL).2 y
  let M := L.tensorPower d
  let D := HilbertConstruction.Ample.LineBundles.sectionNonvanishing s
  have : IsAffine D.toScheme := hs
  obtain ⟨r, hr, hyr⟩ := (isAffineOpen_top D.toScheme).exists_basicOpen_le
    (⟨⟨y, hys⟩, hy⟩ : D.ι ⁻¹ᵁ U) (by trivial)
  obtain ⟨m, _, a, ha⟩ := M.section_extension s r
  let s' : HilbertConstruction.Line.Bundles.structureModule Y ⟶ (M.tensorPower 1).sheaf := s ≫ M.tensorPowerOneIso.inv
  let e : ((M.tensorPower 1).tensor (M.tensorPower m)).sheaf ≅
      (L.tensorPower ((1 + m) * d)).sheaf :=
    (M.tensorPowerAddIso 1 m).symm ≪≫ (L.tensorPowerComposeIso (1 + m) d).symm
  let t := HilbertConstruction.Tensor.ProductSections.tensorProductSection s' a ≫ e.hom
  have ht : HilbertConstruction.Ample.LineBundles.sectionNonvanishing t = D ⊓ HilbertConstruction.Ample.LineBundles.sectionNonvanishing a := by
    exact (HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso _ e).trans
      ((HilbertConstruction.Tensor.SectionNonvanishing.sectionNonvanishing_tensorProduct (M.tensorPower 1) (M.tensorPower m) s' a).trans
        (congrArg (fun V : Y.Opens => V ⊓ HilbertConstruction.Ample.LineBundles.sectionNonvanishing a)
          (HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso s M.tensorPowerOneIso.symm)))
  have hpre : D.ι ⁻¹ᵁ HilbertConstruction.Ample.LineBundles.sectionNonvanishing a = D.toScheme.basicOpen r := by
    have : IsIso (HilbertConstruction.Ample.LineBundles.pullbackSection D.ι (HilbertConstruction.TensorPower.Maps.tensorPowerSection s m)) :=
      HilbertConstruction.Power.Nonvanishing.tensorPowerSection_pullback_isIso D.ι s m
    rw [← HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback]
    exact (HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate
      (HilbertConstruction.Ample.LineBundles.pullbackSection D.ι (HilbertConstruction.TensorPower.Maps.tensorPowerSection s m)) (HilbertConstruction.Ample.LineBundles.pullbackSection D.ι a)).trans
        (congrArg (fun q => D.toScheme.basicOpen q) ha)
  have himage : D.ι ''ᵁ D.toScheme.basicOpen r = HilbertConstruction.Ample.LineBundles.sectionNonvanishing t := by
    rw [← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, ht]
  refine ⟨(1 + m) * d, Nat.mul_pos (by omega) hd, t, ?_, ?_, ?_⟩
  · rw [← himage]
    exact ⟨⟨y, hys⟩, hyr, rfl⟩
  · rw [← himage]
    exact ((isAffineOpen_top D.toScheme).basicOpen r).image_of_isOpenImmersion D.ι
  · rw [← himage]
    rintro z ⟨w, hw, rfl⟩
    exact hr hw

theorem ample_pullback_openImmersion [Y.IsSeparated]
    (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (L : HilbertConstruction.Line.Bundles.LineBundle Y) (hL : L.IsAmple) : (L.pullback j).IsAmple := by
  have hX : IsCompact (Set.univ : Set X) := by
    simpa only [Set.preimage_univ] using
      (QuasiCompact.isCompact_preimage (f := j) Set.univ isOpen_univ hL.1)
  refine ⟨hX, fun x => ?_⟩
  obtain ⟨n, hn, s, hx, hs, hsub⟩ :=
    ample_power_section_neighborhood L hL j.opensRange (j x) ⟨x, rfl⟩
  refine ⟨n, hn, (L.tensorPower n).pullback j,
    (L.tensorPower_isTensorPower n).pullback_of_isOpenImmersion j,
    HilbertConstruction.Ample.LineBundles.pullbackSection j s, ?_, ?_⟩
  · change x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (HilbertConstruction.Ample.LineBundles.pullbackSection j s)
    rw [HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback]
    exact hx
  · change IsAffineOpen (HilbertConstruction.Ample.LineBundles.sectionNonvanishing (HilbertConstruction.Ample.LineBundles.pullbackSection j s))
    rw [HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback]
    exact hs.preimage_of_isOpenImmersion j hsub

theorem ample_pullback_separated_quasiFinite [Y.IsSeparated]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsSeparated f] [QuasiCompact f] (L : HilbertConstruction.Line.Bundles.LineBundle Y) (hL : L.IsAmple) :
    (L.pullback f).IsAmple := by
  have : f.normalization.IsSeparated := ⟨by
    rw [← terminal.comp_from f.fromNormalization]
    infer_instance⟩
  have hN := hL.pullback_of_isAffineHom f.fromNormalization
  have hX := ample_pullback_openImmersion f.toNormalization
    (L.pullback f.fromNormalization) hN
  exact hX.of_iso ((Scheme.Modules.pullbackComp f.toNormalization f.fromNormalization).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr f.toNormalization_fromNormalization).app L.sheaf)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleQuasiFinitePullback
