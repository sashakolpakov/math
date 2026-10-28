import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftOverlap

/-! # Lift Cocycle -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale

noncomputable section

/-! Triple-overlap compatibility for the uniquely lifted etale
transition maps. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X₀ X Y₀ : Scheme.{u}} {i : X₀ ⟶ X} {f₀ : Y₀ ⟶ X₀}
  (A B C : LiftOverlap.Chart i f₀)

def LiftOverlap.Chart.residueAlong {Z Z₀ : Scheme.{u}} (j : Z₀ ⟶ Z)
    (u : Z ⟶ (A.overlap B).toScheme) (v : Z₀ ⟶ A.reduced)
    (h : j ≫ u ≫ (A.overlap B).ι = v ≫ A.reduction) : Z₀ ⟶ B.reduced :=
  (isPullback_morphismRestrict A.reduction (A.overlap B)).lift (j ≫ u) v
    (by simpa only [Category.assoc] using h) ≫ A.residueMap B

@[reassoc] theorem LiftOverlap.Chart.residueAlong_source {Z Z₀ : Scheme.{u}} (j : Z₀ ⟶ Z)
    (u : Z ⟶ (A.overlap B).toScheme) (v : Z₀ ⟶ A.reduced)
    (h : j ≫ u ≫ (A.overlap B).ι = v ≫ A.reduction) :
    A.residueAlong B j u v h ≫ B.source = v ≫ A.source := by
  rw [LiftOverlap.Chart.residueAlong, Category.assoc, LiftOverlap.Chart.residueMap_source, ← Category.assoc, IsPullback.lift_snd]

theorem LiftOverlap.Chart.residueAlong_reduction {Z Z₀ : Scheme.{u}} (j : Z₀ ⟶ Z)
    (u : Z ⟶ (A.overlap B).toScheme) (v : Z₀ ⟶ A.reduced)
    (h : j ≫ u ≫ (A.overlap B).ι = v ≫ A.reduction) :
    j ≫ u ≫ A.transition B = A.residueAlong B j u v h ≫ B.reduction :=
  A.transition_reduction_of B j u v _ h (A.residueAlong_source B j u v h).symm

theorem LiftOverlap.Chart.composition {Z : Scheme.{u}}
    (a : Z ⟶ (A.overlap B).toScheme) (b : Z ⟶ (B.overlap C).toScheme)
    (c : Z ⟶ (A.overlap C).toScheme)
    [IsOpenImmersion (a ≫ (A.overlap B).ι)]
    (hab : a ≫ A.transition B = b ≫ (B.overlap C).ι)
    (hac : a ≫ (A.overlap B).ι = c ≫ (A.overlap C).ι) :
    b ≫ B.transition C = c ≫ A.transition C := by
  let k := a ≫ (A.overlap B).ι
  let j := pullback.snd A.reduction k
  let v := pullback.fst A.reduction k
  have hp : IsPullback j v k A.reduction := (IsPullback.of_hasPullback A.reduction k).flip
  have hj : IsNilpotent j.ker := NilpotentOpenRestriction.nilpotent_of_isPullback
    A.reduction A.nilpotent j v k hp
  have ha : j ≫ a ≫ (A.overlap B).ι = v ≫ A.reduction := hp.w
  have hc : j ≫ c ≫ (A.overlap C).ι = v ≫ A.reduction := by rw [← hac]; exact hp.w
  let vb := A.residueAlong B j a v ha
  let vc := A.residueAlong C j c v hc
  have hb : j ≫ b ≫ (B.overlap C).ι = vb ≫ B.reduction := by
    rw [← hab]
    exact A.residueAlong_reduction B j a v ha
  apply FormallyUnramified.hom_ext j hj C.toBase
  · exact (B.transition_reduction_of C j b vb vc hb
      ((A.residueAlong_source B j a v ha).trans (A.residueAlong_source C j c v hc).symm)).trans
        (A.residueAlong_reduction C j c v hc).symm
  · rw [Category.assoc, LiftOverlap.Chart.transition_base, ← Category.assoc, ← hab,
      Category.assoc, LiftOverlap.Chart.transition_base, ← Category.assoc, hac,
      Category.assoc, Category.assoc, LiftOverlap.Chart.transition_base]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale
