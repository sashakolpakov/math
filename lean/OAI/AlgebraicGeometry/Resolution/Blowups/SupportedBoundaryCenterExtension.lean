import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedAtlasOpenGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhood

/-! # Supported Boundary Center Extension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A local admissible center supported in its open neighborhood remains admissible in the ambient boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.unitCenter
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type}
    {D : β → X.IdealSheafData} {L : List (Finset β)} (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) :
    Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f ⊤ D where
  indices := A.indices
  opens := A.opens
  cover := A.cover
  equations := A.equations
  component := A.component
  divided := fun _ => ∅
  contained := by intro i l hl; exact False.elim (Finset.notMem_empty l hl)
  boundary := A.boundary
  center := by
    intro i q hq
    exact False.elim (q.2.ne_top (top_le_iff.mp hq))

def Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofSupportedOpen
    {V X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (j : V ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) {β : Type} (D : β → X.IdealSheafData) {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L)
    (B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (j ≫ f) (I.comap j) (fun l => (D l).comap j))
    (hsupport : (I.support : Set X) ⊆ Set.range j) : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D := by
  let U : X.Opens := I.support.compl
  let Y : Bool → Scheme := fun b => if b then V else U
  let k : ∀ b, Y b ⟶ X := fun b => match b with
    | false => U.ι
    | true => j
  have hk : ∀ b, IsOpenImmersion (k b) := by intro b; cases b <;> infer_instance
  let C : X.OpenCover := Scheme.Cover.mkOfCovers Bool Y k (by
    intro x
    by_cases hx : x ∈ I.support
    · exact ⟨true, hsupport hx⟩
    · exact ⟨false, ⟨⟨x, hx⟩, rfl⟩⟩) hk
  apply Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofOpenCover f I D C
  intro b
  change Bool at b
  cases b with
  | false =>
      change Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (U.ι ≫ f) (I.comap U.ι) (fun l => (D l).comap U.ι)
      rw [Global.ResidualNeighborhood.Construction.idealSheaf_comap_supportComplement_eq_top]
      exact (A.comapOpen f U.ι).unitCenter
  | true => exact B

def Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.extend_order_supported_center
    {V X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (j : V ⟶ X) [IsOpenImmersion j]
    (J : X.IdealSheafData) (I : V.IdealSheafData) (n : ℕ)
    (hp : J.comap j ≤ I ^ (n + 1))
    (hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support : Set X) ⊆ Set.range j)
    {β : Type} (D : β → X.IdealSheafData) {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L)
    (B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (j ≫ f) I (fun l => (D l).comap j)) :
    Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (Global.OrderCenterExtension.Construction.openCenterExtension j I) D := by
  apply Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofSupportedOpen f j (Global.OrderCenterExtension.Construction.openCenterExtension j I) D A
  · rw [Global.OrderCenterExtension.Construction.order_supported_center_extension_restrict f j J I n hp hcover]
    exact B
  · have hs := SupportedGlobalCenter.Construction.supported_center_kernel_support I.subschemeι j _
      (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support.isClosed
      (Global.OrderCenterExtension.Construction.local_permissible_center_range_in_order_support f j J I n hp) hcover
    intro x hx
    obtain ⟨z, rfl⟩ := hs ▸ hx
    exact ⟨I.subschemeι z, rfl⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
