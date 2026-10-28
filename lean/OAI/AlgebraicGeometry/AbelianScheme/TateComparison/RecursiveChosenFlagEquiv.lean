import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BranchFrameLattice
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FlagRecursion
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LinearFlagRecursion

/-! # Recursive Chosen Flag Equiv -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

section

/-! Recursively construct the geometric-to-chosen-lattice flag bijection
using actual branch lattices and transport of the original source frame.
Compatibility with the separately defined cumulative composite systems
remains a separate proof obligation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  (hg : D.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  {k : Type} [Field k] [IsAlgClosed k] {b : Spec (.of k) ⟶ Spec (.of K)}

def Data.SphericalPELAlbaneseData.recursiveChosenFlagEquiv (ts : List (Local.IntegralType s))
    (x : D.GeometricPoint b) (frame : D.FiberFrame b x)
    (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q
      D.localCharacter frame) :
    D.PELFlag b x ts ≃ Duality.LinearBlockFlags (q : ℤ_[q])
      (fun v => D.framedFiberSourceLattice b x frame (v, false)) ts := by
  induction ts generalizing x with
  | nil =>
    exact {
      toFun _ := Duality.LinearBlockFlags.nil
      invFun _ := Data.SphericalPELAlbaneseData.PELFlag.nil x
      left_inv _ := Subsingleton.elim _ _
      right_inv _ := Subsingleton.elim _ _ }
  | cons t ts ih =>
    let e₁ : (D.correspondence t).Fiber x ≃
        Duality.LinearBlockFlags.NextChoices (q : ℤ_[q])
          (fun v => D.framedFiberSourceLattice b x frame (v, false)) t :=
      D.c46BranchLatticeEquiv x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors hdegree hs
    refine Data.SphericalPELAlbaneseData.PELFlag.consEquiv.trans
      ((Equiv.sigmaCongr e₁ (fun c => ?_)).trans Duality.LinearBlockFlags.consEquiv.symm)
    let y := c.val ≫ (D.correspondence t).target
    let e := D.c46FiberIsogeny hIsogenyQuotient t x y c.val c.property rfl
    let frame' := e.targetFrame q frame
    have hf' : Rational.IsSplitActionFrame (D.fiberFamily b y) (Over.mk (𝟙 (Spec (.of k)))) q
        D.localCharacter frame' := e.targetFrame_equivariant q frame D.localCharacter hf
    have hL : (fun v => D.framedFiberSourceLattice b y frame' (v, false)) =
        fun v => (e₁ c v).val :=
      D.c46Branch_targetFrame_sourceLattice x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors hdegree hs c
    exact (ih y frame' hf').trans
      (Equiv.cast (congrArg (fun L₀ => Duality.LinearBlockFlags (q : ℤ_[q]) L₀ ts) hL))

end

/-! Every later lattice of the recursive bijection is the corresponding
lattice of the tail, expressed in the actually transported source frame.
Changing the proof of the initial-lattice equality preserves all values. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem RecursiveChosenFlagEquiv.linearBlockFlag_cast_val {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    {s : ℕ} (π : R) {L M : Fin s → Duality.RankThreeLattice R K}
    (ts : List (Local.IntegralType s)) (h : L = M) (F : Duality.LinearBlockFlags π L ts) :
    (Equiv.cast (congrArg (fun L₀ => Duality.LinearBlockFlags π L₀ ts) h) F).val = F.val := by
  cases h
  rfl

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  (hg : D.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  {k : Type} [Field k] [IsAlgClosed k] {b : Spec (.of k) ⟶ Spec (.of K)}
  {t : Local.IntegralType s} {ts : List (Local.IntegralType s)}
  (x : D.GeometricPoint b) (frame : D.FiberFrame b x)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q
    D.localCharacter frame)

theorem Data.SphericalPELAlbaneseData.recursiveChosenFlagEquiv_succ (F : D.PELFlag b x (t :: ts)) (j : Fin (ts.length + 1)) :
    let c := Data.SphericalPELAlbaneseData.PELFlag.first F
    let y := c.val ≫ (D.correspondence t).target
    let e := D.c46FiberIsogeny hIsogenyQuotient t x y c.val c.property rfl
    (D.recursiveChosenFlagEquiv hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors
      (t :: ts) x frame hf F).val j.succ =
      (D.recursiveChosenFlagEquiv hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors ts y (e.targetFrame q frame)
        (e.targetFrame_equivariant q frame D.localCharacter hf) (Data.SphericalPELAlbaneseData.PELFlag.tail F)).val j := by
  let c := Data.SphericalPELAlbaneseData.PELFlag.first F
  let y := c.val ≫ (D.correspondence t).target
  let e := D.c46FiberIsogeny hIsogenyQuotient t x y c.val c.property rfl
  let frame' := e.targetFrame q frame
  let G := D.recursiveChosenFlagEquiv hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors ts y frame'
    (e.targetFrame_equivariant q frame D.localCharacter hf) (Data.SphericalPELAlbaneseData.PELFlag.tail F)
  let hL := D.c46Branch_targetFrame_sourceLattice x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors hdegree hs c
  change (Equiv.cast (congrArg (fun L₀ => Duality.LinearBlockFlags (q : ℤ_[q]) L₀ ts) hL) G).val j = G.val j
  exact congrFun (RecursiveChosenFlagEquiv.linearBlockFlag_cast_val (q : ℤ_[q]) ts hL G) j

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
