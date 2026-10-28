import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConcreteChosenFlags
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RecursiveChosenFlagEquiv
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FlagTailComposites

/-! # Recursive Flag Lattices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The recursive geometric flag bijection has exactly the chosen
lattices of the actual cumulative IsogenyQuotient isogenies, at every stage. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  (hg : D.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  {k : Type} [Field k] [IsAlgClosed k] {b : Spec (.of k) ⟶ Spec (.of K)}

theorem Data.SphericalPELAlbaneseData.recursiveChosenFlagEquiv_zero_lattice (ts : List (Local.IntegralType s))
    (x : D.GeometricPoint b) (frame : D.FiberFrame b x)
    (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q
      D.localCharacter frame) (F : D.PELFlag b x ts) (v : Fin s) :
    ((D.recursiveChosenFlagEquiv hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors ts x frame hf F).val 0 v).val =
      D.compositeLattice frame (D.c46FlagComposites hIsogenyQuotient F) 0 (v, false) := by
  have hr := congrArg (fun L => (L v).val)
    (D.recursiveChosenFlagEquiv hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors ts x frame hf F).property.1
  have hc := congrArg (fun L => (L v).val) (D.c46ChosenLattices_zero frame hIsogenyQuotient F)
  exact hr.trans hc.symm

theorem Data.SphericalPELAlbaneseData.recursiveChosenFlagEquiv_lattice (ts : List (Local.IntegralType s)) :
    ∀ (x : D.GeometricPoint b) (frame : D.FiberFrame b x)
      (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q
        D.localCharacter frame) (F : D.PELFlag b x ts) (j : Fin (ts.length + 1)) (v : Fin s),
      ((D.recursiveChosenFlagEquiv hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors ts x frame hf F).val j v).val =
        D.compositeLattice frame (D.c46FlagComposites hIsogenyQuotient F) j (v, false) := by
  induction ts with
  | nil =>
    intro x frame hf F j v
    have hj : j = 0 := Fin.eq_zero j
    subst j
    exact D.recursiveChosenFlagEquiv_zero_lattice hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors [] x frame hf F v
  | cons t ts ih =>
    intro x frame hf F j v
    refine Fin.cases ?_ (fun i => ?_) j
    · exact D.recursiveChosenFlagEquiv_zero_lattice hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors
        (t :: ts) x frame hf F v
    · have hrec := congrArg (fun L => (L v).val)
        (D.recursiveChosenFlagEquiv_succ hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors x frame hf F i)
      refine hrec.trans ?_
      let c := Data.SphericalPELAlbaneseData.PELFlag.first F
      let y := c.val ≫ (D.correspondence t).target
      let e := D.c46FiberIsogeny hIsogenyQuotient t x y c.val c.property rfl
      have htail := ih y (e.targetFrame q frame)
        (e.targetFrame_equivariant q frame D.localCharacter hf) (Data.SphericalPELAlbaneseData.PELFlag.tail F) i v
      refine htail.trans ?_
      change Rational.framedTateLattice (e.targetFrame q frame)
        (D.c46FlagComposites hIsogenyQuotient (Data.SphericalPELAlbaneseData.PELFlag.tail F) i).isogeny.hom (v, false) =
        Rational.framedTateLattice frame (D.c46FlagComposites hIsogenyQuotient F i.succ).isogeny.hom (v, false)
      rw [e.targetFrame_lattice q frame]
      congr 1
      exact (D.c46FlagComposites_tail_hom hIsogenyQuotient F i).symm

theorem Data.SphericalPELAlbaneseData.recursiveChosenFlagEquiv_eq_actual (ts : List (Local.IntegralType s))
    (x : D.GeometricPoint b) (frame : D.FiberFrame b x)
    (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q
      D.localCharacter frame) (F : D.PELFlag b x ts) :
    D.recursiveChosenFlagEquiv hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors ts x frame hf F =
      D.c46ChosenFlag frame hIsogenyQuotient hg hgeometry hf hElementaryDivisors F := by
  apply Subtype.ext
  funext j v
  apply Subtype.ext
  exact D.recursiveChosenFlagEquiv_lattice hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors ts x frame hf F j v

include hdegree hs in
theorem Data.SphericalPELAlbaneseData.c46ChosenFlag_bijective (ts : List (Local.IntegralType s))
    (x : D.GeometricPoint b) (frame : D.FiberFrame b x)
    (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q
      D.localCharacter frame) :
    Function.Bijective (D.c46ChosenFlag (ts := ts) frame hIsogenyQuotient hg hgeometry hf hElementaryDivisors) := by
  have he : D.c46ChosenFlag (ts := ts) frame hIsogenyQuotient hg hgeometry hf hElementaryDivisors =
      D.recursiveChosenFlagEquiv hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors ts x frame hf :=
    funext fun F => (D.recursiveChosenFlagEquiv_eq_actual hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors
      ts x frame hf F).symm
  rw [he]
  exact (D.recursiveChosenFlagEquiv hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors ts x frame hf).bijective

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
