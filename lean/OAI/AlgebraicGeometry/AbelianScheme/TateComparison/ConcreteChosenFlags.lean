import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyFrameTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.InitialFlagLattice
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientConstructedPosition

/-! # Concrete Chosen Flags -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Every actual geometric PEL flag gives an ordinary chosen-block
lattice flag in one source frame. Relative positions are proved by
transporting that frame along the actual cumulative isogenies. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  {k : Type} [Field k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} {x : D.GeometricPoint b}
  {ts : List (Local.IntegralType s)}
  (frame : D.FiberFrame b x) (hIsogenyQuotient : D.RealizesIsogenyQuotient)

def Data.SphericalPELAlbaneseData.c46ChosenLattices (F : D.PELFlag b x ts) (j : Fin (ts.length + 1))
    (v : Fin s) : Duality.RankThreeLattice ℤ_[q] ℚ_[q] :=
  ⟨D.compositeLattice frame (D.c46FlagComposites hIsogenyQuotient F) j (v, false),
    D.flagCompositeLattice_isLattice b x F (D.c46FlagComposites hIsogenyQuotient F) frame j (v, false)⟩

theorem Data.SphericalPELAlbaneseData.c46ChosenLattices_zero (F : D.PELFlag b x ts) :
    D.c46ChosenLattices frame hIsogenyQuotient F 0 =
      fun v => D.framedFiberSourceLattice b x frame (v, false) := by
  funext v
  apply Subtype.ext
  change ((Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
      (D.c46FlagComposites hIsogenyQuotient F 0).isogeny.hom).map
        (frame.toLinearMap.restrictScalars ℤ_[q])).map _ = _
  rw [D.c46FlagComposites_zero_tatePreimage hIsogenyQuotient F]
  rfl

variable (hg : D.IsGoodCompletelySplitPrime) (hgeometry : D.HasIntegralModelGeometry)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q
    D.localCharacter frame)

include hg hgeometry hf in
theorem Data.SphericalPELAlbaneseData.c46ChosenLattices_relativePosition (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (F : D.PELFlag b x ts) (j : Fin ts.length) (v : Fin s) :
    Duality.RelativePosition (q : ℤ_[q]) ((ts.get j).val.exponent v)
      (D.c46ChosenLattices frame hIsogenyQuotient F j.castSucc v)
      (D.c46ChosenLattices frame hIsogenyQuotient F j.succ v) := by
  let p := D.c46FlagComposites hIsogenyQuotient F
  let e := p j.castSucc
  let frame' := e.targetFrame q frame
  have hf' : Rational.IsSplitActionFrame (D.fiberFamily b (F.point j.castSucc))
      (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame' :=
    e.targetFrame_equivariant q frame D.localCharacter hf
  obtain ⟨M, hM, hpos⟩ := D.c46Fiber_projectedRelativePosition b (F.point j.castSucc)
    frame' hg hgeometry hIsogenyQuotient (ts.get j) (F.point j.succ)
    (F.branch j) (F.source j) (F.target j) hf' hElementaryDivisors v
  have hsource : D.framedFiberSourceLattice b (F.point j.castSucc) frame' (v, false) =
      D.c46ChosenLattices frame hIsogenyQuotient F j.castSucc v := by
    apply Subtype.ext
    change (Rational.framedIntegralTateImage (e.targetFrame q frame)).map _ = _
    rw [e.targetFrame_integral q frame]
    rfl
  have htarget : M = D.c46ChosenLattices frame hIsogenyQuotient F j.succ v := by
    apply Subtype.ext
    rw [hM]
    change Rational.framedTateLattice (e.targetFrame q frame) (D.c46FlagSteps hIsogenyQuotient F j).isogeny.hom
      (v, false) = _
    rw [e.targetFrame_lattice q frame]
    have hcomp := D.compositeFromSteps_succ_hom F (D.c46FlagSteps hIsogenyQuotient F) j
    change (p j.succ).isogeny.hom = e.isogeny.hom ≫ (D.c46FlagSteps hIsogenyQuotient F j).isogeny.hom at hcomp
    change Rational.framedTateLattice frame (e.isogeny.hom ≫ (D.c46FlagSteps hIsogenyQuotient F j).isogeny.hom)
      (v, false) = Rational.framedTateLattice frame (p j.succ).isogeny.hom (v, false)
    congr 1
    exact hcomp.symm
  rw [hsource, htarget] at hpos
  exact hpos

def Data.SphericalPELAlbaneseData.c46ChosenFlag (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (F : D.PELFlag b x ts) :
    Duality.LinearBlockFlags (q : ℤ_[q])
      (fun v => D.framedFiberSourceLattice b x frame (v, false)) ts :=
  ⟨D.c46ChosenLattices frame hIsogenyQuotient F, D.c46ChosenLattices_zero frame hIsogenyQuotient F,
    D.c46ChosenLattices_relativePosition frame hIsogenyQuotient hg hgeometry hf hElementaryDivisors F⟩

theorem Data.SphericalPELAlbaneseData.c46ChosenFlag_lattice (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (F : D.PELFlag b x ts)
    (j : Fin (ts.length + 1)) (v : Fin s) :
    ((D.c46ChosenFlag frame hIsogenyQuotient hg hgeometry hf hElementaryDivisors F).val j v).val =
      D.compositeLattice frame (D.c46FlagComposites hIsogenyQuotient F) j (v, false) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
