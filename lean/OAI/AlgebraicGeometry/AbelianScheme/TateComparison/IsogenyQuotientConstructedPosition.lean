import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.QuotientFramedLatticeType
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionFromKernel
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexIntegralBlocks

/-! # Isogeny Quotient Constructed Position -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientConstructedPosition.SphericalPELAlbaneseData

noncomputable section

/-! Actual IsogenyQuotient isogenies have the prescribed chosen relative positions
in the constructed complex source frame. The source lattices are the
projected actual integral Tate images, with no integral-frame hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  {k : Type} [Field k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)
  (frame : D.FiberFrame b x)

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.framedFiberSourceLattice (v : Fin s × Bool) : Duality.RankThreeLattice ℤ_[q] ℚ_[q] := by
  have := D.fiberIntegralTateImage_isLattice b x
  exact ⟨D.framedSourceLattice (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) frame v,
    D.framedSourceLattice_isLattice (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) frame v⟩

variable (hg : D.IsGoodCompletelySplitPrime) (hgeometry : D.HasIntegralModelGeometry)
  (h : D.RealizesIsogenyQuotient) (t : Local.IntegralType s) (y : D.GeometricPoint b)
  (c : Over.mk b ⟶ (D.correspondence t).cover)
  (hsource : c ≫ (D.correspondence t).source = x)
  (htarget : c ≫ (D.correspondence t).target = y)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)

include hg hgeometry hf in
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.c46Fiber_projectedRelativePosition (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (v : Fin s) :
    ∃ M : Duality.RankThreeLattice ℤ_[q] ℚ_[q],
      M.val = Rational.framedTateLattice frame (D.c46FiberIsogeny h t x y c hsource htarget).isogeny.hom (v, false) ∧
      Duality.RelativePosition (q : ℤ_[q]) (t.val.exponent v)
        (D.framedFiberSourceLattice b x frame (v, false)) M := by
  let e := D.c46FiberIsogeny h t x y c hsource htarget
  have : Submodule.IsLattice ℚ_[q]
      (Rational.integralTateImage (D.fiberFamily b y).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :=
    D.fiberIntegralTateImage_isLattice b y
  have hfull := IsogenyLattices.framedTateLattice_isLattice
    (A := (D.fiberFamily b x).abelian) (B := (D.fiberFamily b y).abelian)
    (𝟙 (Spec (.of k))) q frame e.isogeny (v, false)
  let M : Duality.RankThreeLattice ℤ_[q] ℚ_[q] := ⟨Rational.framedTateLattice frame e.isogeny.hom (v, false), hfull⟩
  let L := D.framedFiberSourceLattice b x frame (v, false)
  have hLM : L.val ≤ M.val :=
    D.framedSourceLattice_le_target hg e frame hf D.reference.polarizationType
      (D.fiberPolarizationType hgeometry b x) hg.2.2.2.2 (v, false)
  have hgroup := D.c46FiberFramedLatticeQuotientType hg hgeometry h t x y c hsource htarget frame hf v
  unfold Data.SphericalPELAlbaneseData.framedTateLatticeQuotient Data.SphericalPELAlbaneseData.sourceInFramedTateLattice at hgroup
  have ha : Antitone (t.exponentNat v) := fun i j hij => Int.toNat_le_toNat (t.val.dominant v hij)
  refine ⟨M, rfl, ?_⟩
  have hpos := RelativePositionFromKernel.relativePosition_of_quotient_type q hElementaryDivisors L M hLM (t.exponentNat v) ha hgroup
  simpa only [Local.IntegralType.exponentNat_cast] using hpos

local notation "fiberBase" => Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField))

variable (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (bC : fiberBase ⟶ Spec (.of K)) (xC yC : D.GeometricPoint bC)
  (cC : Over.mk bC ⟶ (D.correspondence t).cover)
  (hcsource : cC ≫ (D.correspondence t).source = xC)
  (hctarget : cC ≫ (D.correspondence t).target = yC)

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.complexIsogenyQuotient_relativePosition (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (v : Fin s) :
    ∃ M : Duality.RankThreeLattice ℤ_[q] ℚ_[q],
      M.val = Rational.framedTateLattice (D.complexSplitFrame hg hdegree hs hgeometry bC xC)
        (D.c46FiberIsogeny h t xC yC cC hcsource hctarget).isogeny.hom (v, false) ∧
      Duality.RelativePosition (q : ℤ_[q]) (t.val.exponent v)
        (D.complexBlockLattice hg hdegree hgeometry hs bC xC (v, false)) M :=
  D.c46Fiber_projectedRelativePosition bC xC (D.complexSplitFrame hg hdegree hs hgeometry bC xC)
    hg hgeometry h t yC cC hcsource hctarget
    (D.complexSplitFrame_equivariant hg hdegree hs hgeometry bC xC) hElementaryDivisors v

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientConstructedPosition.SphericalPELAlbaneseData
