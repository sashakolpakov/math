import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricFieldModel
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitFrameTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexSplitEquivariance

/-! # Geometric Split Frame -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricSplitFrame.SphericalPELAlbaneseData

noncomputable section

/-! Compatible split Tate frames for all geometric PEL fibers. A
countable algebraically closed field of definition connects each fiber
to a complex fiber; both comparisons are actual Tate isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

local notation "fiberBase" => Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField))

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)

include hg hdegree hs in
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.exists_frame_of_common_complex_model
    {L k : Type} [Field L] [CharZero L] [IsAlgClosed L] [Field k]
    (bk : Spec (.of k) ⟶ Spec (.of L)) (bc : fiberBase ⟶ Spec (.of L))
    (P : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level (Spec (.of L)))
    (Pk : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level (Spec (.of k)))
    (Pc : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level fiberBase)
    (ak : PELModuli.PELFamilyIso Pk (P.pullback bk)) (ac : PELModuli.PELFamilyIso Pc (P.pullback bc))
    (Qc : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation Pc.abelian.scheme) :
    ∃ e : Rational.SplitTateFrame s Pk.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q,
      Rational.IsSplitActionFrame Pk (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter e := by
  obtain ⟨ec, hc⟩ := D.exists_split_frame_of_complex_base hg hdegree hs
    (S := fiberBase) rfl Pc Qc
  let ec' := ac.symm.transportFrame (Over.mk (𝟙 fiberBase)) ec
  have hc' := ac.symm.transportFrame_equivariant (Over.mk (𝟙 fiberBase)) D.localCharacter ec hc
  let eL := SplitFrameTransport.descendFieldFrame bc P ec'
  have hL := SplitFrameTransport.descendFieldFrame_equivariant bc P D.localCharacter ec' hc'
  let ek' := SplitFrameTransport.extendFieldFrame bk P D.localCharacter eL hL
  have hk' := SplitFrameTransport.extendFieldFrame_equivariant bk P D.localCharacter eL hL
  exact ⟨ak.transportFrame (Over.mk (𝟙 (Spec (.of k)))) ek',
    ak.transportFrame_equivariant (Over.mk (𝟙 (Spec (.of k)))) D.localCharacter ek' hk'⟩

variable (h : D.HasIntegralModelGeometry)
  {k : Type} [Field k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)

include hg hdegree hs h in
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.geometricSplitFrame_exists :
    ∃ e : D.FiberFrame b x,
      Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter e := by
  have : Countable K := Cardinal.mk_le_aleph0_iff.mp
    ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ K).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl))
  have : Smooth D.model.space.hom := h.smooth
  have : LocallyOfFiniteType D.space.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd D.model.space.hom D.generic))
  obtain ⟨M⟩ := GeometricFieldModel.geometricPoint_has_countable_model K D.space.hom x.left
  let bk := Spec.map (CommRingCat.ofHom M.toOriginal)
  let bc : fiberBase ⟶ Spec (.of M.field) := Spec.map (CommRingCat.ofHom M.toComplex)
  let bL := M.point ≫ D.space.hom
  let xc : D.GeometricPoint (bc ≫ bL) := Over.homMk (bc ≫ M.point) (Category.assoc _ _ _)
  exact D.exists_frame_of_common_complex_model hg hdegree hs bk bc
    (D.family.pullback M.point) (D.fiberFamily b x) (D.fiberFamily (bc ≫ bL) xc)
    (D.family.pullbackFactor bk M.point x.left M.factor)
    (D.family.pullbackFactor bc M.point (bc ≫ M.point) rfl)
    (D.fiberProjectivePresentation h (bc ≫ bL) xc)

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.geometricSplitFrame : D.FiberFrame b x :=
  (D.geometricSplitFrame_exists hg hdegree hs h b x).choose

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.geometricSplitFrame_equivariant :
    Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter
      (D.geometricSplitFrame hg hdegree hs h b x) :=
  (D.geometricSplitFrame_exists hg hdegree hs h b x).choose_spec

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricSplitFrame.SphericalPELAlbaneseData
