import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FramedPreimageDecomposition
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricCompositeDetermination

/-! # Geometric Block Determination -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

section

/-! Equality of the actual framed block lattices determines a literal
polarized marked composite over every algebraically closed field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  (hg : D.IsGoodCompletelySplitPrime) (hgeometry : D.HasIntegralModelGeometry)
  {k : Type} [Field k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} {x : D.GeometricPoint b}
  {ts : List (Local.IntegralType s)}
  (frame : D.FiberFrame b x)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q
    D.localCharacter frame)

include hg hgeometry hf in
theorem Data.SphericalPELAlbaneseData.geometricCompositeDatum_eq_of_blocks_eq (a c : D.CompositeDatum x ts)
    (h : ∀ v, Rational.framedTateLattice frame a.2.isogeny.hom v =
      Rational.framedTateLattice frame c.2.isogeny.hom v) : a = c := by
  apply D.geometricCompositeDatum_eq_of_preimage_eq hg hgeometry a c
  exact D.preimage_eq_of_framedTateLattice_eq hg a.2 frame hf
    D.reference.polarizationType (D.fiberPolarizationType hgeometry b x)
    hg.2.2.2.2 c.2 h

end

/-! Once actual flags realize the chosen and opposite lattices, their
literal composite depends only on the final chosen lattices. The proof
uses all geometric PEL rigidity and the full Tate preimage decomposition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  (hg : D.IsGoodCompletelySplitPrime) (hgeometry : D.HasIntegralModelGeometry)
  {k : Type} [Field k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} {x : D.GeometricPoint b}
  {ts : List (Local.IntegralType s)}
  (frame : D.FiberFrame b x)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q
    D.localCharacter frame)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient)
  (B : Fin s → LinearMap.BilinForm ℚ_[q] (Fin 3 → ℚ_[q]))
  (L₀ : Fin s → Duality.RankThreeLattice ℤ_[q] ℚ_[q])

include hg hgeometry hf in
theorem Data.SphericalPELAlbaneseData.realizedFlag_composite_eq_of_terminal_eq
    {F F' : D.PELFlag b x ts} {L L' : Duality.LinearBlockFlags (q : ℤ_[q]) L₀ ts}
    {c c' : D.CompositeDatum x ts}
    (hF : D.RealizesLinearFlag hIsogenyQuotient frame B L₀ F L c)
    (hF' : D.RealizesLinearFlag hIsogenyQuotient frame B L₀ F' L' c')
    (hL : L.val (Fin.last ts.length) = L'.val (Fin.last ts.length)) : c = c' := by
  obtain ⟨p, f, hp, rfl, hblocks⟩ := hF
  obtain ⟨p', f', hp', rfl, hblocks'⟩ := hF'
  apply D.geometricCompositeDatum_eq_of_blocks_eq hg hgeometry frame hf
  rintro ⟨v, side⟩
  have hv : (L.val (Fin.last ts.length) v).val = (L'.val (Fin.last ts.length) v).val :=
    congrArg (fun a => (a v).val) hL
  cases side
  · exact ((hblocks (Fin.last ts.length) v).1.trans hv).trans
      (hblocks' (Fin.last ts.length) v).1.symm
  · change D.compositeLattice frame p (Fin.last ts.length) (v, true) =
      D.compositeLattice frame p' (Fin.last ts.length) (v, true)
    rw [(hblocks (Fin.last ts.length) v).2, (hblocks' (Fin.last ts.length) v).2, hv]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
